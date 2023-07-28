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
module Data.Cone.TH where

import Data.Char
import Data.Cone
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
      let f = mkName "f"
      case cons of
        [] -> fail $ "makeDiagram currently does not support: " <> show c
        [RecC n fs] ->
          do
            pure
            <$> dataInstD
              (pure [])
              ''Diagram
              [theType, varT f]
              Nothing
              [ recC
                  (mkName $ mkDiagramName (nameBase name))
                  [ vbType n' [t|$(varT f) $(pure t)|]
                  | (n', _, t) <- fs
                  ]
              ]
              []
        cons -> do
          pure
            <$> dataInstD
              (pure [])
              ''Diagram
              [theType, varT f]
              Nothing
              [ recC
                  (mkName $ mkDiagramName (nameBase name))
                  [ case con of
                    NormalC n ts' -> covbType n [t|$(varT f) $(tupleD (map snd ts'))|]
                    _ -> fail $ "makeDiagram currently does not constructors of: " <> show con
                  | con <- cons
                  ]
              ]
              []
    a -> fail $ "makeDiagram currently does not support: " <> show a
 where
  mkDiagramName idt = idt <> "D"
  mkCoconname idt = "if" <> idt
  mkConname (a : idt) = "get" <> (toUpper a : idt)
  mkConname [] = fail "unexpected empty field name"

  tupleD = \case
    [] -> [t|()|]
    [t] -> pure t
    ts -> mkTupleT (map pure ts)

  covbType n = varBangType (mkName . mkCoconname $ nameBase n) . bangType (bang noSourceUnpackedness noSourceStrictness)

  vbType n = varBangType (mkName . mkConname $ nameBase n) . bangType (bang noSourceUnpackedness noSourceStrictness)

mkType :: Name -> [Name] -> Q Type
mkType n = foldl (\a t -> a `appT` varT t) (conT n)

typeNames :: [TyVarBndr flag] -> [Name]
typeNames = map \case
  PlainTV t _ -> t
  KindedTV t _ _ -> t

mkTupleT :: Quote m => [m Type] -> m Type
mkTupleT ts = foldl appT (conT $ tupleTypeName (length ts)) ts
