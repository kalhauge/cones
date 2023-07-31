{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
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

{- | Given a name of an ADT, we can generate a corresponding 'Diagram' with
correct cones and limits.
-}
makeDiagram :: Name -> Q [Dec]
makeDiagram name = do
  TyConI c <- reify name
  case c of
    DataD [] _ ts Nothing cons _ -> do
      let theTypeNames = typeNames ts
      let theType = mkType name theTypeNames
      -- let theDiagramType = [t|Diagram $theType|]
      let f = mkName "f"
      case cons of
        [] -> fail $ "makeDiagram currently does not support: " <> show c
        [RecC cn fs] -> do
          let diagramName = mkName $ mkDiagramName (nameBase name)
          diagramFields <-
            sequence
              [ pure (mkName . mkConname $ nameBase n, n, ts')
              | -- _ -> fail $ "makeDiagram currently does not constructors of: " <> show con
              (n, _, ts') <- fs
              ]
          sequence
            [ dataInstD
                (pure [])
                ''Diagram
                [theType, varT f]
                Nothing
                [ recC
                    diagramName
                    [ vbType n [t|$(varT f) $(pure ts')|]
                    | (n, _, ts') <- diagramFields
                    ]
                ]
                ( [derivClause (Just StockStrategy) [[t|Generic|]]]
                    <> [ derivClause
                          (Just AnyclassStrategy)
                          [[t|FunctorB|], [t|ApplicativeB|], [t|TraversableB|]]
                       ]
                )
            , instanceD
                (pure [])
                [t|IsLimit $theType|]
                [ do
                    valD
                      (varP 'cone)
                      ( normalB
                          ( recConE
                              diagramName
                              [ fieldExp n (varE cn)
                              | (n, cn, _) <- diagramFields
                              ]
                          )
                      )
                      []
                , do
                    valD
                      (varP 'coneCone)
                      ( normalB
                          ( recConE
                              diagramName
                              [ fieldExp n [e|\a -> $(varE n) a ()|]
                              | (n, _, _) <- diagramFields
                              ]
                          )
                      )
                      []
                , do
                    diag <- newName "diag"
                    a <- newName "a"
                    funD
                      'factor
                      [ clause
                          [varP diag, varP a]
                          ( normalB $
                              recConE
                                cn
                                [ fieldExp n' [e|$(varE n) $(varE diag) $(varE a)|]
                                | (n, n', _) <- diagramFields
                                ]
                          )
                          []
                      ]
                ]
            ]
        _ -> do
          let diagramName = mkName $ mkDiagramName (nameBase name)
          diagramConstructors <-
            sequence
              [ case con of
                NormalC n ts' -> pure (mkName . mkCoconname $ nameBase n, n, ts')
                _ -> fail $ "makeDiagram currently does not constructors of: " <> show con
              | con <- cons
              ]

          sequence
            [ dataInstD
                (pure [])
                ''Diagram
                [theType, varT f]
                Nothing
                [ recC
                    diagramName
                    [ covbType n [t|$(varT f) $(tupleD (map snd ts'))|]
                    | (n, _, ts') <- diagramConstructors
                    ]
                ]
                ( [derivClause (Just StockStrategy) [[t|Generic|]]]
                    <> [ derivClause
                          (Just AnyclassStrategy)
                          [[t|FunctorB|], [t|ApplicativeB|], [t|TraversableB|]]
                       ]
                )
            , instanceD
                (pure [])
                [t|IsColimit $theType|]
                [ do
                    valD
                      (varP 'cocone)
                      ( normalB
                          ( recConE
                              diagramName
                              [ fieldExp n (opConE cn t)
                              | (n, cn, t) <- diagramConstructors
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
                                  [ opConM cn t (\t -> [e|getOp ($(varE n) $(varE diag)) $t|])
                                  | (n, cn, t) <- diagramConstructors
                                  ]
                              )
                          )
                          []
                      ]
                ]
            ]
    a -> fail $ "makeDiagram currently does not support: " <> show a
 where
  -- sequence
  --   [ standaloneDerivWithStrategyD (Just StockStrategy) (pure []) (varT t `appT` theType)
  --   | t <- [''Eq, ''Show, ''Generic]
  --   ]

  mkDiagramName idt = idt <> "D"
  mkCoconname idt = "if" <> idt
  mkConname (a : idt) = "get" <> (toUpper a : idt)
  mkConname [] = fail "unexpected empty field name"

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

  tupleD = \case
    [] -> [t|()|]
    [t] -> pure t
    ts -> mkTupleT (map pure ts)

  tupleElimE fn = \case
    0 -> [e|(const $fn)|]
    1 -> [e|$fn|]
    2 -> [e|(uncurry $fn)|]
    n -> do
      nms <- replicateM n (newName "a")
      let mt = tupP [varP nm | nm <- nms]
      lamE [mt] (foldl (\a nm -> a `appE` varE nm) fn nms)

  covbType n = varBangType n . bangType (bang noSourceUnpackedness noSourceStrictness)

  vbType n = varBangType n . bangType (bang noSourceUnpackedness noSourceStrictness)

mkType :: Name -> [Name] -> Q Type
mkType n = foldl (\a t -> a `appT` varT t) (conT n)

typeNames :: [TyVarBndr flag] -> [Name]
typeNames = map \case
  PlainTV t _ -> t
  KindedTV t _ _ -> t

mkTupleT :: Quote m => [m Type] -> m Type
mkTupleT ts = foldl appT (conT $ tupleTypeName (length ts)) ts
