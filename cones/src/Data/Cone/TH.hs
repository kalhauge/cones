{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module: Data.Cone.TH

A module for generating diagrams, cones, and limits.
-}
module Data.Cone.TH (
  makeDiagram,
  module Barbies,
) where

-- barbies
import Barbies

import Control.Monad
import Data.Char
import Data.Cone
import Data.Functor.Contravariant
import GHC.Generics
import Language.Haskell.TH

data DiagramSpec a = DiagramSpec
  { dsType :: Type
  , dsConstructorName :: Name
  , dsFieldNames :: [(Name, a, Type)]
  }

makeDiagramFromSpec :: DiagramSpec a -> Q Dec
makeDiagramFromSpec DiagramSpec{..} = do
  let f = mkName "f"
  dataInstD
    (pure [])
    ''Diagram
    [pure dsType, varT f]
    Nothing
    [ recC
        dsConstructorName
        [ covbType n (varT f `appT` pure ts)
        | (n, _, ts) <- dsFieldNames
        ]
    ]
    [ derivClause
        (Just StockStrategy)
        [[t|Generic|]]
    , derivClause
        (Just AnyclassStrategy)
        [[t|FunctorB|], [t|ApplicativeB|], [t|TraversableB|]]
    ]

makeLimitFromSpec :: Name -> DiagramSpec Name -> Q Dec
makeLimitFromSpec cn DiagramSpec{..} =
  instanceD
    (pure [])
    [t|IsLimit $(pure dsType)|]
    [ valD (varP 'cone) makeCone []
    , valD (varP 'coneCone) makeConecone []
    , funD 'factor [makeFactor]
    ]
 where
  makeCone =
    normalB $
      recConE
        dsConstructorName
        [ fieldExp n (varE cn')
        | (n, cn', _) <- dsFieldNames
        ]

  makeConecone =
    normalB $
      recConE
        dsConstructorName
        [ fieldExp n [e|\a -> $(varE n) a ()|]
        | (n, _, _) <- dsFieldNames
        ]
  makeFactor = do
    diag <- newName "diag"
    a <- newName "a"
    clause
      [varP diag, varP a]
      ( normalB $
          recConE
            cn
            [ fieldExp n' [e|$(varE n) $(varE diag) $(varE a)|]
            | (n, n', _) <- dsFieldNames
            ]
      )
      []
makeColimitFromSpec :: DiagramSpec (Name, [Type]) -> Q Dec
makeColimitFromSpec DiagramSpec{..} =
  instanceD
    (pure [])
    [t|IsColimit $(pure dsType)|]
    [ do
        valD
          (varP 'cocone)
          ( normalB
              ( recConE
                  dsConstructorName
                  [ fieldExp n (opConE cn ts)
                  | (n, (cn, ts), _) <- dsFieldNames
                  ]
              )
          )
          []
    , do
        diag <- newName "diag"
        a <- newName "a"
        funD
          'cofactor
          [ clause
              [varP diag, varP a]
              ( normalB
                  ( caseE
                      (varE a)
                      [ opConM cn ts (\t' -> [e|getOp ($(varE n) $(varE diag)) $t'|])
                      | (n, (cn, ts), _) <- dsFieldNames
                      ]
                  )
              )
              []
          ]
    ]
 where
  opConE cn t =
    [e|Op $(tupleElimE (conE cn) (length t))|]

  opConM cn ts fn = do
    nms <- sequence [newName "a" | _ <- ts]
    match
      (conP cn [varP n | n <- nms])
      (normalB (fn (tupleE [varE n | n <- nms])))
      []

  tupleE = \case
    [] -> [e|()|]
    [v] -> v
    vs -> tupE vs

  tupleElimE fn = \case
    0 -> [e|(const $fn)|]
    1 -> [e|$fn|]
    2 -> [e|(uncurry $fn)|]
    n -> do
      nms <- replicateM n (newName "a")
      let mt = tupP [varP nm | nm <- nms]
      lamE [mt] (foldl (\a nm -> a `appE` varE nm) fn nms)

makeBLensesForDiagram :: DiagramSpec a -> Q Dec
makeBLensesForDiagram DiagramSpec{..} =
  instanceD
    (pure [])
    [t|LensesB (Diagram $(pure dsType))|]
    [ valD
        (varP 'blenses)
        ( normalB $
            recConE
              dsConstructorName
              [ fieldExp n [e|BLens $ \fn b -> (\x -> $(recUpdE (varE 'b) [fieldExp n (varE 'x)])) <$> fn ($(varE n) b)|]
              | (n, _, _) <- dsFieldNames
              ]
        )
        []
    ]

{- | Given a name of an ADT, we can generate a corresponding 'Diagram' with
correct cones and limits.
-}
makeDiagram :: Name -> Q [Dec]
makeDiagram name = do
  TyConI c <- reify name
  (ts, cons) <- case c of
    DataD [] _ ts Nothing cons _ -> do
      pure (ts, cons)
    a -> fail $ "makeDiagram currently does not support: " <> show a

  let theTypeNames = typeNames ts
  dsType <- mkType name theTypeNames
  -- let theDiagramType = [t|Diagram $theType|]
  case cons of
    [] -> fail $ "makeDiagram currently does not support: " <> show c
    [RecC cn fs] -> do
      let dsConstructorName = mkName $ mkDiagramName (nameBase name)
      dsFieldNames <-
        sequence
          [ pure (mkName . mkConname $ nameBase n, n, ts')
          | -- _ -> fail $ "makeDiagram currently does not constructors of: " <> show con
          (n, _, ts') <- fs
          ]
      let diagramSpec = DiagramSpec{..}
      sequence
        [ makeDiagramFromSpec diagramSpec
        , makeLimitFromSpec cn diagramSpec
        , makeBLensesForDiagram diagramSpec
        ]
    _ -> do
      let dsConstructorName = mkName $ mkDiagramName (nameBase name)
      dsFieldNames <-
        sequence
          [ case con of
            NormalC n ts' -> do
              t <- tupleD (map snd ts')
              pure (mkName . mkCoconname $ nameBase n, (n, map snd ts'), t)
            _ -> fail $ "makeDiagram currently does not constructors of: " <> show con
          | con <- cons
          ]
      let diagramSpec = DiagramSpec{..}
      sequence
        [ makeDiagramFromSpec diagramSpec
        , makeColimitFromSpec diagramSpec
        , makeBLensesForDiagram diagramSpec
        ]
 where
  mkDiagramName idt = idt <> "D"
  mkCoconname idt = "if" <> idt
  mkConname (a : idt) = "get" <> (toUpper a : idt)
  mkConname [] = fail "unexpected empty field name"

  tupleD = \case
    [] -> [t|()|]
    [t] -> pure t
    ts -> mkTupleT (map pure ts)

covbType :: Quote m => Name -> m Type -> m VarBangType
covbType n = varBangType n . bangType (bang noSourceUnpackedness noSourceStrictness)

mkType :: Name -> [Name] -> Q Type
mkType n = foldl (\a t -> a `appT` varT t) (conT n)

typeNames :: [TyVarBndr flag] -> [Name]
typeNames = map \case
  PlainTV t _ -> t
  KindedTV t _ _ -> t

mkTupleT :: Quote m => [m Type] -> m Type
mkTupleT ts = foldl appT (conT $ tupleTypeName (length ts)) ts
