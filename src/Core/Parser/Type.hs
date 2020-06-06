{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes           #-}
module Core.Parser.Type
  where

import Data.Text hiding (empty, foldr, foldl', length, null, splitAt, span)
import Data.Void
import Prelude hiding (unlines)
import Control.Monad (void)
import Data.Char
import Control.Applicative (liftA2)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Text.Parsec.Char as Char
import Text.Parsec (Parsec, SourcePos, many)
import qualified Text.Parsec as Parsec
import Control.Applicative hiding (many)

import Core.Expression
import Core.Parser.Util
import Core.Parser.Lex



parseTyUnit :: Parser (Type String)
parseTyUnit = TyUnit <$ token LUnit


parseVar :: Parser String
parseVar =
  do
    LVar var <- fmap getToken $ satisfy isTokVar
    pure var

parseTyVar :: Parser (Type String)
parseTyVar =
  do
    LVar var <- fmap getToken $ satisfy isTokVar
    pure (TyVar var)

parseForAll :: Parser (Type String)
parseForAll =
  do
    LForAll var <- fmap getToken $ satisfy isForAll
    ty  <- parseType
    pure $ ForAll var ty

parsePrimType :: Parser (Type String)
parsePrimType = do
  Parsec.choice
    [ parseTyUnit
    , parseTyVar
    ]

parseArr :: Parser (Type String)
parseArr =
  do
    ty1 <- parsePrimType
    token LArr
    ty2 <- parseType
    pure (TyArr ty1 ty2)

parseType :: Parser (Type String)
parseType = do
  ty <- Parsec.choice
    [ parseTyUnit
    , parseForAll
    , Parsec.try parseArr
    , parseTyVar
    ]
  Parsec.eof
  pure ty
