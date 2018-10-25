{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
module Lib where

import           Bound
import           Control.Lens hiding ( Context )
import           Control.Lens.Operators
import           Data.Deriving ( deriveEq1, deriveShow1 )
import           Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import           Data.Scientific ( Scientific )
import           Data.Text ( Text )
import qualified Data.Text as T
import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char as MPC
import qualified Text.Megaparsec.Char.Lexer as MPCL

import           Control.Applicative ( (<|>) )
import           Data.Bifunctor ( bimap )
import           Data.Char ( isAsciiUpper, isAsciiLower, isDigit )
import           Data.Foldable ( foldl' )
import           Data.Void ( Void )

data AtomicPrim
  = APBool Bool
  | APNum Scientific
  | APStr Text
  | APExc Text
  deriving ( Show, Eq )

data AtomicPrimTy
  = APTBool
  | APTNum
  | APTStr
  | APTExc
  deriving ( Show, Eq )

data Exp a
  = EVar a
  | ELam (Scope () Exp a)
  | (Exp a) :@: (Exp a)
  | EAP AtomicPrim
  | EAPT AtomicPrimTy
  | EType
  | (Exp a) :-> (Scope () Exp a)
  | (Exp a) ::: (Exp a)
  deriving ( Functor, Foldable, Traversable )

deriveEq1 ''Exp
deriveShow1 ''Exp
makeBound ''Exp

deriving instance (Show a) => Show (Exp a)
deriving instance (Eq a) => Eq (Exp a)

exp1 :: Exp String
exp1 = ELam (Scope (EVar (F (EVar "y"))))

exp2 :: Exp String
exp2 = ELam (Scope (ELam (Scope (EVar (F (EVar (F (EVar "g"))))))))

exp3 :: Exp String
exp3 = ELam (Scope (ELam (Scope (EVar (F (EVar (B ())))))))

exp4 :: Exp String
exp4 = ELam (Scope (EVar (F (ELam (Scope (EVar (F (EVar "g"))))))))
 
data EvalErr a
  = InScope (EvalErr (Var () a))
  | InvalidApp (Exp a) (Exp a)
  | InvalidFunctionType (Exp a)
  | TypeMismatch (Exp a) (Exp a)
  | CannotInfer (Exp a)
  | UnknownVar a
  | MistypedLambda (Exp a) (Exp a)
  deriving ( Show, Eq, Functor, Foldable, Traversable )

norm :: Exp a -> Either (EvalErr a) (Exp a)
norm = \case
  e ::: ty -> norm e
  ELam body -> ELam <$> normUnderBinder body
  fun :@: arg -> do
    fun' <- norm fun 
    arg' <- norm arg
    case fun' of
      ELam body -> norm $ instantiate1 arg' body
      v@(EVar _) -> pure $ v :@: arg'
      _ -> Left $ InvalidApp fun' arg'
  ty :-> depTy -> (:->) <$> norm ty <*> normUnderBinder depTy
  e -> pure e
  where
    normUnderBinder = bimap InScope toScope . norm . fromScope

type Context a = [(a, Exp a)]

primType :: AtomicPrim -> AtomicPrimTy
primType = \case
  APBool _ -> APTBool
  APNum _ -> APTNum
  APStr _ -> APTStr
  APExc _ -> APTExc

check
  :: (Eq a)
  => Context a
  -> Exp a -> Exp a
  -> Either (EvalErr a) (Exp a)
check ctx e ty = case e of
  ELam body -> case ty of
    argTy :-> depTy -> do
      bimap InScope toScope $ check
        ((B (), F <$> argTy):(ctx & traverse._1 %~ F
                                  & traverse._2.mapped %~ F))
        (fromScope body)
        (fromScope depTy)
      pure ty
  _ -> do
    infTy <- infer ctx e
    if infTy == ty
      then pure ty
      else Left $ TypeMismatch ty infTy

infer :: (Eq a) => Context a -> Exp a -> Either (EvalErr a) (Exp a)
infer ctx = \case
  EVar a -> case lookup a ctx of
    Just ty -> pure ty
    Nothing -> Left $ UnknownVar a
  l@(ELam _) -> Left $ CannotInfer l
  fun :@: arg -> do
    funTy <- infer ctx fun
    case funTy of
      argTy :-> depTy -> do
        check ctx arg argTy
        norm $ instantiate1 arg depTy
      _ -> Left $ InvalidFunctionType fun
  ann@(e ::: ty) -> do
    ty' <- norm ty
    check ctx e ty'
  argTy :-> depTy -> do
    check ctx argTy EType
    argTy' <- norm argTy
    bimap InScope (const EType) $ check
      ((B (), F <$> argTy'):(ctx & traverse._1 %~ F
                                 & traverse._2.mapped %~ F))
      (fromScope depTy)
      EType
  EAP ap -> pure $ EAPT $ primType ap
  EAPT apt -> pure EType
  EType -> pure EType

lam :: (Eq a) => a -> Exp a -> Exp a
lam = (ELam .) . abstract1

forall_ :: (Eq a) => a -> Exp a -> Exp a -> Exp a
forall_ v argTy depTy = argTy :-> abstract1 v depTy

type Parser = MP.Parsec Void Text

symbol :: Text -> Parser Text
symbol = MPCL.symbol MPC.space

lexeme :: Parser a -> Parser a
lexeme = MPCL.lexeme MPC.space

pStrLit :: Parser Text
pStrLit = MP.label "string literal" $ lexeme $ do 
  MPC.char '"'
  T.concat <$> plainContents
  where
    notEscOrEnd = \case
      '\\' -> False
      '"'  -> False
      _    -> True
    plainContents
      = (:)
      <$> MP.takeWhileP (Just "string literal character") notEscOrEnd
      <*> escOrEnd
    escOrEnd = MPC.anyChar >>= \case
      '\\' -> escSeq
      '"' -> pure []
    escSeq = MPC.anyChar >>= \case
      '\\' -> ("\\":) <$> plainContents
      '"'  -> ("\"":) <$> plainContents
      _    -> fail "Invalid escape sequence"

pNumLit :: Parser Scientific
pNumLit
  = MP.label "numeric literal"
  $ lexeme
  $ MPCL.signed (pure ()) MPCL.scientific
  
inParens :: Parser a -> Parser a
inParens = MP.between (symbol "(") (symbol ")")

reserved :: [Text]
reserved
  = [ "match", "with"
    , "if", "then", "else"
    -- , "is"
    , "and", "or", "not"
    , "true", "false"
    , "null"
    , "empty"
    ]

pIdentifier' :: Parser Text
pIdentifier'
  = MP.try
  $ checkReserved
  =<< T.cons
  <$> (MPC.lowerChar <|> MPC.upperChar <|> MPC.char '_')
  <*> MP.takeWhileP (Just "identifier character")
        (\c -> isAsciiUpper c || isAsciiLower c || isDigit c || c == '_')
  where
    checkReserved id_ = if id_ `elem` reserved
      then fail $ T.unpack id_ <> " is a reserved word\
                                  \ and cannot be used as an identifier"
      else pure id_

pIdentifier :: Parser Text
pIdentifier = lexeme pIdentifier'

type Exp' = Exp Text

pDecl :: Parser (Text, Exp')
pDecl = do
  name <- pIdentifier
  symbol "="
  (,) <$> pure name <*> pExp

pExp :: Parser Exp'
pExp = fmap (foldl1 (:@:)) $ MP.some $ do
  e <- MP.choice [pVar, pLambda, pPi, pLit, inParens pExp]
  symbol ":" *> ((e :::) <$> pExp)
    <|> pure e

pVar :: Parser Exp'
pVar = EVar <$> pIdentifier

pLambda :: Parser Exp'
pLambda = do
  symbol "\\"
  args <- MP.some pIdentifier
  symbol "."
  body <- pExp
  pure $ foldr ((ELam .) . abstract1) body args

pLit :: Parser Exp'
pLit
  = fmap EAP
  $ MP.choice
    [ APStr <$> pStrLit
    , APNum <$> pNumLit
    , APBool <$> ((True <$ symbol "true") <|> (False <$ symbol "false"))
    ]

pPi :: Parser Exp'
pPi = do
  symbol "/\\"
  args <- MP.some pIdentifier
  symbol ":"
  argTy <- pExp
  symbol "."
  depTy <- pExp
  pure $ foldr (((argTy :->) .) . abstract1) depTy args

type Env a = [(a, Exp a)]

prelude :: Env Text
prelude =
  [ ("Type", EType)
  , ("Bool", EAPT APTBool)
  , ("Number", EAPT APTNum)
  , ("String", EAPT APTStr)
  ]

pInput :: Env Text -> Parser (String, Env Text)
pInput env = MP.try processDecl <|> processExp
  where
    processDecl = do
      (name, e) <- pDecl
      let e' = foldl' (flip $ uncurry substitute) e env
      case infer [] e' of
        Left err -> pure (show err, env)
        Right ty -> case norm e' of
          Left err -> pure (show err, env)
          Right e'' -> let name' = T.unpack name in
            pure ( name' <> " ::: " <> show ty
                   <> "\n" <> name' <> " = " <> show e''
                 , (name, e'):env
                 )
    processExp = do
      e <- pExp
      let e' = foldl' (flip $ uncurry substitute) e env
      case infer [] e' of
        Left err -> pure (show err, env)
        Right ty -> case norm e' of
          Left err -> pure (show err, env)
          Right e'' -> pure (show (e'' ::: ty), env)

repl :: IO ()
repl = repl' prelude
  where
    repl' env = do
      putStr "> "
      line <- getLine
      if null line
        then pure ()
        else case MP.parse (pInput env) "" (T.pack line) of
          Left err -> do
            putStrLn "Parse error:"
            putStrLn $ MP.parseErrorPretty err
            repl' env
          Right (msg, env') -> do
            putStrLn msg
            repl' env'

