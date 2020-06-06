{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes           #-}
module Core.Parser.Term
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
import Core.Expression
import Core.Parser.Util
import Core.Parser.Lex
import Core.Parser.Type


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
