{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
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

import Barbies.Access
import Control.Monad
import Data.Char
import Data.Cone
import Data.Functor.Const
import Data.Functor.Contravariant
import GHC.Generics
import Language.Haskell.TH

data DiagramSpec a = DiagramSpec
  { dsType :: Type
  , dsConstructorName :: Name
  , dsFieldNames :: [(Name, a, Type)]
  }
  deriving (Functor)

makeDiagramFromSpec :: DiagramSpec a -> Q [Dec]
makeDiagramFromSpec DiagramSpec{..} =
  pure <$> do
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

makeIndexedFromSpec :: DiagramSpec a -> Q [Dec]
makeIndexedFromSpec DiagramSpec{..} = do
  indexedB <-
    instanceD
      (pure [])
      [t|IndexedB (Diagram $(pure dsType))|]
      [ valD
          (varP 'bindexed)
          ( normalB $
              foldl
                (\a (n, _) -> a `appE` [e|$(conE 'Const) $(litE $ integerL n)|])
                (conE dsConstructorName)
                (zip [0 ..] dsFieldNames)
          )
          []
      ]
  ixBs <-
    sequence
      [ instanceD
        (pure [])
        [t|IxB (Diagram $(pure dsType)) $(litT (numTyLit i)) $(pure t)|]
        [funD 'bix [clause [[p|Index|]] (normalB $ varE n) []]]
      | (i, (n, _, t)) <-
          zip [0 ..] dsFieldNames
      ]

  pure (indexedB : ixBs)

makeLabeledFromSpec :: DiagramSpec Name -> Q [Dec]
makeLabeledFromSpec DiagramSpec{..} = do
  indexedB <-
    instanceD
      (pure [])
      [t|LabeledB (Diagram $(pure dsType))|]
      [ valD
          (varP 'blabeled)
          ( normalB $
              foldl
                (\a (_, cn, _) -> a `appE` [e|$(conE 'Const) $(litE $ stringL (nameBase cn))|])
                (conE dsConstructorName)
                dsFieldNames
          )
          []
      ]
  ixBs <-
    sequence
      [ instanceD
        (pure [])
        [t|HasB (Diagram $(pure dsType)) $(litT (strTyLit (nameBase cn))) $(pure t)|]
        [funD 'bfrom [clause [[p|Label|]] (normalB $ varE n) []]]
      | (n, cn, t) <- dsFieldNames
      ]

  pure (indexedB : ixBs)

makeLimitFromSpec :: Name -> DiagramSpec Name -> Q [Dec]
makeLimitFromSpec cn DiagramSpec{..} =
  pure
    <$> instanceD
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

makeColimitFromSpec :: DiagramSpec (Name, [Type]) -> Q [Dec]
makeColimitFromSpec DiagramSpec{..} =
  pure
    <$> instanceD
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

makeLensesBForDiagram :: DiagramSpec a -> Q [Dec]
makeLensesBForDiagram DiagramSpec{..} =
  pure
    <$> instanceD
      (pure [])
      [t|LensesB (Diagram $(pure dsType))|]
      [ valD
          (varP 'blenses)
          ( normalB $
              recConE
                dsConstructorName
                [ fieldExp n [e|$(conE 'ALensB) $ \fn b -> (\x -> $(recUpdE (varE 'b) [fieldExp n (varE 'x)])) <$> fn ($(varE n) b)|]
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
      concat
        <$> sequence
          [ makeDiagramFromSpec diagramSpec
          , makeLimitFromSpec cn diagramSpec
          , makeLensesBForDiagram diagramSpec
          , makeIndexedFromSpec diagramSpec
          , makeLabeledFromSpec diagramSpec
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
      concat
        <$> sequence
          [ makeDiagramFromSpec diagramSpec
          , makeColimitFromSpec diagramSpec
          , makeLensesBForDiagram diagramSpec
          , makeIndexedFromSpec diagramSpec
          , makeLabeledFromSpec (fmap fst diagramSpec)
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
