{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes           #-}
module Core.Parser
  (
    lexTerm
  , Token
  , parseTerm
  , parseType
  ) where

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

import System.IO.Unsafe
import Debug.Trace

data Info = Info
  { fileName :: Maybe String
  , pos      :: SourcePos
  }
  deriving (Show, Eq, Ord)

getInfo :: Parsec s u Info
getInfo =
  do
    pos <- Parsec.getPosition
    pure $ Info Nothing pos

type Lexer a = Parsec String () a
type Parser a = Parsec [Token] () a

data Token' v =
    LVar v
  | LeftB
  | RightB
  | LUnit
  | LForAll v
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

addInfo :: Lexer (Token' String) -> Lexer Token
addInfo lexer = liftA2 (,) lexer getInfo


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


parseTerm :: Parser (Term Text)
parseTerm = undefined


token :: Token' String -> Parser Token
token token = satisfy match
  where
    match t | t == token = Just t
    match _ = Nothing


satisfy :: (Token' String -> Maybe (Token' String)) -> Parser Token
satisfy match = Parsec.tokenPrim pr nextSrcPos match'
  where
    match' (t, inf) =
      do
        m <- match t
        pure (m, inf)
    pr = tokenPretty
    nextSrcPos pos _ _ = pos




-- |
-- This ignores spaces and tabs.
space :: Lexer ()
space = () <$ Parsec.space


spaceEOF :: Lexer ()
spaceEOF = (() <$ Parsec.space) <|> Parsec.eof




--wsIgnore :: Lexer ()
--wsIgnore = L.space wSpaceP lineComment blockComment

--sIgnore :: Lexer ()
--sIgnore = L.space spaceP lineComment blockComment


lexeme :: ()
  => Parsec s u ()              -- ^ How to consume white space after lexeme
  -> Parsec s u a               -- ^ How to parse actual lexeme
  -> Parsec s u a
lexeme spc p = p <* spc
{-# INLINEABLE lexeme #-}


lexemeWS :: Lexer a -> Lexer a
lexemeWS = lexeme (Parsec.skipMany space)

lexemeEOF :: Lexer a -> Lexer a
lexemeEOF = lexeme (Parsec.skipMany spaceEOF)



ident :: Lexer String
ident = lexemeWS ((:) <$> Parsec.lower <*> many Parsec.alphaNum)


dot :: Lexer ()
dot = void $ lexemeWS (Parsec.char ('.'))


colon :: Lexer ()
colon = void $ lexemeWS (Parsec.char (':'))


leftBracket :: Lexer ()
leftBracket = void $ lexemeWS (Parsec.char ('('))

rightBracket :: Lexer ()
rightBracket = void $ lexemeWS (Parsec.char (')'))

keyword :: String -> Lexer ()
keyword str = void $ lexemeWS (Parsec.string str)




{-
var :: Lexer (Term Text)
var = Var <$> ident


lam :: Lexer (Term Text)
lam =
  do
    void $ lexemeS (char '\\')
    vars <- some ident
    void $ lexemeS (char '.')
    body <- parseExpr
    let lamExpr = foldr Lam body vars
    pure lamExpr


parseUnit :: Lexer (Term Text)
parseUnit = bracketed parseExpr <|> lam <|> var

app :: Lexer (Term Text)
app =
  do
    left  <- parseUnit
    rest  <- some parseUnit
    let appExpr = foldl' App left rest
    pure appExpr


parseExpr :: Lexer (Term Text)
parseExpr =
  choice
    [ lam
    , (try app)
    , var
    , bracketed parseExpr
    ]
-}

{-
sepEndBy1 :: Lexer a -> Lexer sep -> Lexer [a]
sepEndBy1 p sep = do{ x <- p
                    ; do{ _ <- sep
                        ; xs <- sepEndBy p sep
                        ; return (x:xs)
                        }
                      <|> return [x]
                    }
-}
{-

programExample :: Text
programExample = unlines ["f = {1}", "", "g = {let {x = 1; y = 2} 2}"]

blockExample :: Text
blockExample = "g = let {x = a; y = b} w"

lamEx :: Text
lamEx = "\\x . x"
-}
