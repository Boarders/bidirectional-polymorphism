{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes           #-}
module Core.Parser.Lex
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


type Lexer a = Parsec String () a
type Parser a = Parsec [Token] () a

data Token' v =
    LVar v
  | LeftB
  | RightB
  | LUnit
  | LForAll v
  | LAnn
  | LArr
  | LFun
  | LMapsTo
  | LHasTy
  deriving (Eq, Ord, Show)

isTokVar :: Token' v -> Maybe (Token' v)
isTokVar var@(LVar _) = Just var
isTokVar  _       = Nothing

isForAll :: Token' v -> Maybe (Token' v)
isForAll ty@(LForAll _) = Just ty
isForAll  _       = Nothing

tokenPretty :: Token -> String
tokenPretty = show


type Token = (Token' String, Info)

getToken = fst


tokenVar :: Lexer Token
tokenVar = addInfo (LVar <$> ident)

tokenUnit :: Lexer Token
tokenUnit = addInfo (LUnit <$ (keyword "()"))


tokenForAll :: Lexer Token
tokenForAll = addInfo $
  LForAll <$>
    do
      keyword "forall"
      var <- ident
      dot
      pure var

tokenArr :: Lexer Token
tokenArr = addInfo $ LArr <$ keyword "->"

tokenFun :: Lexer Token
tokenFun = addInfo $ LFun <$ keyword "fun"

tokenMapsTo :: Lexer Token
tokenMapsTo = addInfo $ LMapsTo <$ keyword "=>"

tokenHasTy :: Lexer Token
tokenHasTy = addInfo $ LHasTy <$ colon

tokenLeftBracket :: Lexer Token
tokenLeftBracket = addInfo $ LeftB <$ leftBracket

tokenRightBracket :: Lexer Token
tokenRightBracket = addInfo $ RightB <$ rightBracket

lexTerm :: Lexer [Token]
lexTerm =
  do
    Parsec.skipMany space
    toks <- Parsec.many $
      Parsec.choice
        [ tokenUnit
        , tokenForAll
        , tokenVar
        , tokenArr
        , tokenFun
        , tokenMapsTo
        , tokenHasTy
        , tokenLeftBracket
        , tokenRightBracket
        ]
    Parsec.eof
    pure toks
