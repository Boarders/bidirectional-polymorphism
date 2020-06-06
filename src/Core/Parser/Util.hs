{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE FlexibleContexts   #-}
module Core.Parser.Util
  where

import Data.Text hiding (empty, foldr, foldl', length, null, splitAt, span)
import Data.Void
import Prelude hiding (unlines)
import Control.Monad (void)
import Data.Char
import Control.Applicative (liftA2)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Text.Parsec.Char as Char
import Text.Parsec (Parsec, SourcePos, many, Stream, ParsecT)
import qualified Text.Parsec as Parsec
import Control.Applicative hiding (many)
import Data.Functor.Identity


data Info = Info
  { fileName :: Maybe String
  , pos      :: SourcePos
  }
  deriving (Show, Eq, Ord)

getInfo :: Monad m => ParsecT s u m Info
getInfo =
  do
    pos <- Parsec.getPosition
    pure $ Info Nothing pos

addInfo :: Monad m => ParsecT s u m a -> ParsecT s u m (a, Info)
addInfo p = liftA2 (,) p getInfo


token :: (Eq token, Stream s m (token, Info), Show token) => token -> ParsecT s u m (token, Info)
token token = satisfy match
  where
    match t | t == token = Just t
    match _ = Nothing


satisfy
  :: (Stream s m (token, Info), Show token)
  => (token -> Maybe token) -> ParsecT s u m (token, Info)
satisfy match = Parsec.tokenPrim show nextSrcPos match'
  where
    match' (t, inf) =
      do
        m <- match t
        pure (m, inf)
    nextSrcPos pos _ _ = pos




-- |
-- This ignores spaces and tabs.
space :: Stream s Identity Char => Parsec s u ()
space = () <$ Parsec.space


spaceEOF :: Stream s Identity Char => Parsec s u ()
spaceEOF = (() <$ Parsec.space) <|> Parsec.eof

lexeme :: ()
  => ParsecT s u m ()              -- ^ How to consume white space after lexeme
  -> ParsecT s u m a               -- ^ How to parse actual lexeme
  -> ParsecT s u m a
lexeme spc p = p <* spc
{-# INLINEABLE lexeme #-}


lexemeWS :: Stream s Identity Char => Parsec s u a -> Parsec s u a
lexemeWS = lexeme (Parsec.skipMany space)

lexemeEOF :: Stream s Identity Char => Parsec s u a -> Parsec s u a
lexemeEOF = lexeme (Parsec.skipMany spaceEOF)



ident :: Stream s Identity Char => Parsec s u String
ident = lexemeWS ((:) <$> Parsec.lower <*> many Parsec.alphaNum)


dot :: Stream s Identity Char => Parsec s u ()
dot = void $ lexemeWS (Parsec.char ('.'))


colon :: Stream s Identity Char => Parsec s u ()
colon = void $ lexemeWS (Parsec.char (':'))


leftBracket :: Stream s Identity Char => Parsec s u ()
leftBracket = void $ lexemeWS (Parsec.char ('('))

rightBracket :: Stream s Identity Char => Parsec s u ()
rightBracket = void $ lexemeWS (Parsec.char (')'))

keyword :: Stream s Identity Char => String -> Parsec s u ()
keyword str = void $ lexemeWS (Parsec.string str)
