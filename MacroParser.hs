
{-# LANGUAGE BangPatterns, ExistentialQuantification #-}

--import Prelude hiding (fold,foldr,foldl,foldl',foldr',foldl1,foldr1)

--module MacroParser2
import qualified Control.Monad
import qualified Control.Monad.State.Strict as State
import Control.Monad.State.Strict (StateT)
import qualified Data.ByteString.Char8 as BS
import Data.ByteString.Char8 (ByteString)
import qualified Data.Char
import qualified Data.Foldable
import qualified Data.Maybe
import Data.Maybe (Maybe)
import qualified Data.Sequence as Seq
import Data.Sequence (Seq, (|>), (<|), (><), ViewL(..), ViewR(..))
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Traversable
import qualified Data.Trie as Trie
import qualified Data.Trie.Internal as TrieInternal
import Data.Trie (Trie)
import qualified System.Environment

import Debug.Trace

type StringT = Seq Char
type BuiltinT = ParseState -> (ExpressionL, ParseState)

data MacroDef = User !ExpressionL
 | Builtin !BuiltinT

instance Show MacroDef where
 show (User x) = "(User (" ++ show x ++ "))"
 show (Builtin _) = "(Builtin _)"
type MacroMap = Trie [Maybe MacroDef]
data ParseState = ParseState {
 inputSeq :: !ExpressionL,
 macroMap :: !MacroMap
} deriving (Show)

standardMacros = Trie.fromList [
 (BS.pack "_cleanup", [Just $ Builtin cleanup]),
 (BS.pack "pushDef" , [Just $ Builtin pushDefBuiltin]),
 (BS.pack "popDef"  , [Just $ Builtin popDefBuiltin]),
 (BS.pack "quote"   , [Just $ Builtin quoteBuiltin]),
 (BS.pack "setDef"  , [Just $ Builtin setDefBuiltin])]
standardParseState str = ParseState (Seq.singleton $ Sequence $ Seq.fromList str) standardMacros

--instance Show ParseState where
-- show (Par)

getInput :: (Monad m) => StateT ParseState m ExpressionL
getInput = do
 state <- State.get
 return $ inputSeq state
modifyInput :: (Monad m) => (ExpressionL->ExpressionL) -> StateT ParseState m ()
modifyInput f = State.modify $ \s -> s {inputSeq = f $ inputSeq s}
setInput :: (Monad m) => ExpressionL -> StateT ParseState m ()
setInput input = State.modify $ \s -> s {inputSeq = input}

getMacros :: (Monad m) => StateT ParseState m MacroMap
getMacros = do
 state <- State.get
 return $ macroMap state
modifyMacros :: (Monad m) => (MacroMap -> MacroMap) -> StateT ParseState m ()
modifyMacros f = State.modify $ \s -> s {macroMap = f $ macroMap s}
setMacros macros = State.modify $ \s -> s {macroMap = macros}

type ExpressionL = Seq Expression
data Expression = Null
 | Sequence !StringT
 | Special !Char
 | Quote !ExpressionL
 | Paren !ExpressionL
 | Macro !Expression !(Seq ExpressionL)
 deriving (Show)

toOutputString = stringFromStringT . toOutputStringExprL
toOutputStringExprL :: ExpressionL -> StringT
toOutputStringExprL aL = Data.Foldable.foldl' (><) Seq.empty $ fmap toOutputStringExpr aL
toOutputStringExpr :: Expression -> StringT
toOutputStringExpr (Sequence s) = s
toOutputStringExpr (Quote aL) = (<|) '[' $ toOutputStringExprL aL |> ']'
toOutputStringExpr (Paren aL) = (<|) '(' $ toOutputStringExprL aL |> ')'
toOutputStringExpr (Special c) = Seq.singleton c
toOutputStringExpr a = error $ "error: toOutputStringExpr " ++ show a

stringFromStringT :: StringT -> String
stringFromStringT = Data.Foldable.foldr (:) []
byteStringFromStringT = BS.pack . stringFromStringT

setDefs :: (Monad m) => ByteString -> [Maybe MacroDef] -> StateT ParseState m ()
setDefs name defs = modifyMacros $ Trie.insert name defs

getDefsMaybe :: (Monad m) => ByteString -> StateT ParseState m (Maybe [Maybe MacroDef])
getDefsMaybe name = do
 macros <- getMacros
 return $ Trie.lookup name macros

nothingToError :: Maybe a -> a
nothingToError (Just a) = a
nothingToError Nothing = error "nothingToError Nothing"

getDefs :: (Monad m) => ByteString -> StateT ParseState m [Maybe MacroDef]
getDefs name = getDefsMaybe name >>= return . nothingToError
getDefsDefault :: (Monad m) => ByteString -> StateT ParseState m [Maybe MacroDef]
getDefsDefault name = getDefsMaybe name >>= return . Data.Maybe.fromMaybe []

getDefMaybe :: (Monad m) => ByteString -> StateT ParseState m (Maybe MacroDef)
getDefMaybe name = do
 defs <- getDefsDefault name
 if null defs then
  return Nothing
 else if Data.Maybe.isNothing (head defs) then
  return Nothing
 else do
  return . head $ defs
getDef :: (Monad m) => ByteString -> StateT ParseState m MacroDef
getDef name = getDefMaybe name >>= return . nothingToError

--expandMaybe :: a -> a -> Maybe b -> a
--expandMaybe x _ Nothing  = x
--expandMaybe _ y (Just _) = y

setDef :: (Monad m) => ByteString -> Maybe MacroDef -> StateT ParseState m ()
--setDef name !def = do
-- modifyMacros $ Trie.adjust ((:) def . Data.Maybe.fromMaybe []) name
setDef name !def = do
 defs <- getDefsDefault name
 let defs' = if null defs then [def] else def : tail defs
 setDefs name defs'

pushDef :: (Monad m) => ByteString -> Maybe MacroDef -> StateT ParseState m ()
pushDef name !def = do
 defs <- getDefsDefault name
 setDefs name (def:defs)

pushUserDef name def = pushDef name (fmap User def)

popDef :: (Monad m) => ByteString -> StateT ParseState m ()
popDef name = do
 defs <- getDefsDefault name
 if null defs then do
  --don't
  error $ "popDef " ++ show name ++ ": null defs"
 else if null (tail defs) then do
  modifyMacros $ Trie.delete name
 else setDefs name (tail defs)

specialChars = Set.fromList [',',' ','\n','\t','\r','\f','\v']
isSpecialChar c = Set.member c specialChars

parseExpressionL = parseExpressionL' Seq.empty Seq.empty
parseExpressionL' :: (Monad m) => ExpressionL -> StringT -> StateT ParseState m ExpressionL
parseExpressionL' !resultL !resultStr = do
 input <- getInput
 if Seq.null input then
  return $ if Seq.null resultStr then resultL else resultL |> Sequence resultStr
 else do
  let input1 :< inputL = Seq.viewl input
  case input1 of
   Sequence s -> do
    if Seq.null s then do
     setInput inputL
     parseExpressionL' resultL resultStr
    else do
     let
      x1:<xL = Seq.viewl s
      input' = Sequence xL <| inputL
     setInput input'
     if x1 == ']' || x1 == ')' then do
      return (if Seq.null resultStr then resultL else resultL |> Sequence resultStr)
     else if x1 == '[' then do
      let resultStrHelper = if Seq.null resultStr then Seq.empty else Seq.singleton $ Sequence resultStr
      quot <- parseExpressionL' Seq.empty Seq.empty
      parseExpressionL' (concatSequences $ Seq.fromList [resultL,resultStrHelper,Seq.singleton $ Quote quot]) Seq.empty
     else if x1 == '(' then do
      let resultStrHelper = if Seq.null resultStr then Seq.empty else Seq.singleton $ Sequence resultStr
      paren <- parseExpressionL' Seq.empty Seq.empty
      parseExpressionL' (concatSequences $ Seq.fromList [resultL,resultStrHelper,Seq.singleton $ Paren paren]) Seq.empty
     else if isSpecialChar x1 then do
      parseExpressionL' (if Seq.null resultStr then resultL |> Special x1 else resultL |> Sequence resultStr |> Special x1) Seq.empty
     else do
      parseExpressionL' resultL (resultStr |> x1)

--stringToParseTree s = State.evalState parseExpressionL (ParseState (Seq.singleton (Sequence (Seq.fromList s))) Trie.empty)
stringToParseTree s = State.evalState parseExpressionL (standardParseState s)
--bob = stringToParseTree "a[b]c"

processTree :: (Monad m) => ExpressionL -> StateT ParseState m ExpressionL
processTree tree = do
 old <- getInput
 setInput tree
 result <- processInput
 setInput old
 return result

processInput :: (Monad m) => StateT ParseState m ExpressionL
processInput = do
 input <- getInput
 if Seq.null input then
  return Seq.empty
 else do
  let (i1:<iL) = Seq.viewl input
  setInput iL
  case i1 of
--   Special ']' -> return Seq.empty
   Special c -> do
    tail <- processInput
    return $ (Special c) <| tail
   Quote e -> do
    tail <- processInput
    return $ e >< tail
   Paren e -> do
    e' <- processTree e
    tail <- processInput
    return $ Paren e' <| tail
   Sequence s -> do
    if Seq.null s then do
     setInput iL
     processInput
    else do
     let s1:<sL = Seq.viewl s
     setInput input
     b <- parseMacro
     if b then do
      processInput
     else do
      setInput $ Sequence sL <| iL
      tail <- processInput
      if Seq.null tail then
       return $ Seq.singleton $ Sequence $ Seq.singleton s1
      else do
       let t1:<tL = Seq.viewl tail
       case t1 of
        Sequence seq2 -> return $ Sequence (s1<|seq2) <| tL
        _ -> return $ Sequence (Seq.singleton s1) <| tail
   Macro name args -> do
    callMacro name args

callMacro (Sequence name) args = do
 definition <- getDef $ byteStringFromStringT name
-- let expansion = Data.Maybe.fromJust $ Trie.lookup (BS.pack $ Data.Foldable.foldr (:) [] name) macroTable --TODO: builtin vs custom
 cleanup <- setupArgs name args
 input <- getInput
 case definition of
  User expansion -> do
   expansion' <- processTree expansion
   setInput (cleanup >< input)
   tail <- processInput
   return $ expansion' >< tail
--   setInput $ expansion >< cleanup >< input
--   processInput
  Builtin operation -> do
   --do NOT schedule cleanup, because otherwise infinite loop with cleanup after cleanup
--   let input2 = cleanup >< input
--   setInput input2
   state <- State.get
   let (result,state2) = operation state
   State.put state2
   input2 <- getInput
   setInput $ result >< input2
   processInput

setupArgs :: (Monad m) => StringT -> Seq ExpressionL -> StateT ParseState m ExpressionL
setupArgs name args = do
 oldArgCount <- getArgCount
 let argCount = Seq.length args
 pushUserDef (BS.pack "$@") . Just . intercalate (Special ',') $ args
 pushUserDef (BS.pack "$#") . Just . Seq.singleton . Sequence . Seq.fromList . show $ argCount
 pushUserDef (BS.pack "$0") . Just . Seq.singleton . Sequence  $ name
 pushArgs (1::Int) args
 maskArgs (argCount+1) oldArgCount
 return $ Seq.fromList [Sequence $ Seq.fromList "_cleanup", Special ' ']
 where
  intercalate separator args
   | Seq.null args = Seq.empty
   | otherwise = helper Seq.empty args
   where
    helper !result args = let arg1:<argL = Seq.viewl args in
     if Seq.length args == 1 then
      result |> Quote arg1
     else helper (flip (|>) separator $ result >< arg1) argL
  pushArgs !n args
   | Seq.null args = return ()
   | otherwise = do
      let arg1:<argL = Seq.viewl args
      pushUserDef (BS.pack $ "$" ++ show n) (Just arg1)
      pushArgs (n+1) argL
  maskArgs arg max = maskArgs' arg where
   _ = (arg,max) :: (Int,Int)
   maskArgs' arg =
    if arg <= max then do
     pushUserDef (BS.pack $ "$" ++ show arg) Nothing
     maskArgs' (arg+1)
    else don't

don't :: Monad m => m ()
don't = return ()

parseMacro :: (Monad m) => StateT ParseState m Bool
parseMacro = do
 macroName <- parseLongestMacro
 if Seq.null macroName then do
  return False
 else do
  arguments <- parseMacroArguments
  input <- getInput
--  arguments' <- Data.Traversable.mapM processTree arguments
  setInput $ Macro (Sequence macroName) arguments <| input
  return True

parseLongestMacro :: (Monad m) => StateT ParseState m StringT
parseLongestMacro = do
 macros <- getMacros
 input <- getInput
 if Seq.null input then
  return Seq.empty
 else do
  let i1:<iL = Seq.viewl input
  case i1 of
   Sequence _ -> do
    result <- helper Seq.empty macros
    if Seq.null result then do
     setInput input
    else don't
    return result
   _ -> return Seq.empty
 where
  helper !result !macros = do
   input <- getInput
   if Seq.null input then
    return result
   else do
    if Trie.null macros then
     return Seq.empty
    else do
     let (Sequence s):<iL = Seq.viewl input
     if Trie.member BS.empty macros then do
      longer <- helper result (Trie.delete BS.empty macros)
      if Seq.null longer then do
       setInput input
       return result
      else return longer
     else if Seq.null s then
      return Seq.empty
     else do
      let s1:<sL = Seq.viewl s
      setInput $ Sequence sL <| iL
      helper (result|>s1) (trieReducer (BS.singleton s1) macros)

trieReducer :: ByteString -> Trie a -> Trie a
trieReducer prefix names = TrieInternal.lookupBy_ (\a tr -> if Data.Maybe.isJust a then Trie.insert BS.empty (Data.Maybe.fromJust a) tr else tr) Trie.empty id prefix names

parseMacroArguments :: (Monad m) => StateT ParseState m (Seq ExpressionL)
parseMacroArguments = do
 input <- getInput
 if Seq.null input then
  return Seq.empty
 else do
  let i1:<iL = Seq.viewl input
  case i1 of
   Paren eL -> do
    eL' <- processTree eL
    setInput eL'
    result <- parseArgs Seq.empty
    setInput iL
    return result
   Sequence s -> do
    if Seq.null s then do
     setInput iL
     parseMacroArguments
    else return Seq.empty
   _ -> return Seq.empty
parseArgs !result = do
 input <- getInput
 if Seq.null input then
  return result
 else do
  let i1:<iL = Seq.viewl input
  case i1 of
   Special c ->
    if Data.Char.isSpace c then do
     setInput iL
     parseArgs result
    else do
     arg <- parseArg Seq.empty
     arg' <- processTree arg
     parseArgs $ result |> arg'
   _ -> do
    arg <- parseArg Seq.empty
    arg' <- processTree arg
    parseArgs $ result |> arg'
parseArg !result = do
 input <- getInput
 if Seq.null input then
  return result
 else do
  let i1:<iL = Seq.viewl input
  setInput iL
  case i1 of
   Special c ->
    if c == ',' then do
     return result
    else parseArg $ result |> i1
   _ -> parseArg $ result |> i1

concatSequences :: Seq (Seq a) -> Seq a
concatSequences = Data.Foldable.foldl' (><) Seq.empty

builtinHelper x = do
 state <- State.get
 let (result,state') = x state
 State.put state'
 return result

getArgCount :: (Monad m) => StateT ParseState m Int
getArgCount = do
 argCount1 <- getDefMaybe (BS.pack "$#")
 let
  argCount2 = do
   arg <- argCount1
   arg2 <- case arg of
    User a -> return a
    _ -> Nothing
   let arg3 = toOutputString arg2
   return (read arg3)
  argCount = Data.Maybe.fromMaybe (-1) argCount2
--  argCount = Data.Maybe.fromMaybe (-1) argCount2
-- Debug.Trace.traceShow argCount $ return argCount
 return argCount

--TODO: could be slightly more efficient by walking down the Trie to the place where all the $ things are
cleanup :: ParseState -> (ExpressionL,ParseState)
cleanup state0 = State.runState helper state0 where
 helper = {-Debug.Trace.trace "\n\n\n\n" $ Debug.Trace.traceShow state0 $-} do
--  argCount1 <- getDefMaybe
  --pop the arguments passed to the cleanup function itself
  popDef (BS.pack "$@")
  popDef (BS.pack "$#")
  popDef (BS.pack "$0")
  argCount <- getArgCount
--  argCount' <- getArgCount
--  argCount <- Debug.Trace.trace ("\ncleanup: argCount="++show argCount'++"\n") $ return argCount'
  popDef (BS.pack "$@")
  popDef (BS.pack "$#")
  popDef (BS.pack "$0")
  oldArgCount <- getArgCount
--  oldArgCount' <- getArgCount
--  oldArgCount <- Debug.Trace.trace ("\ncleanup: oldArgCount="++show oldArgCount'++"\n") $ return oldArgCount'
  popArgs 1 (argCount::Int)
  popArgs 1 (argCount::Int)
  popArgs (1+argCount) oldArgCount
  input <- getInput
  if Seq.null input then
   error "null input in cleanup"
  else do
   let i1:<iL = Seq.viewl input
   case i1 of
    Special ' ' -> do
     setInput iL
    _ -> error "Did not find space after cleanup!"
  state <- State.get
--  Debug.Trace.traceShow state $ return Seq.empty
  return Seq.empty
 popArgs n max =
  if n <= max then do
   popDef . BS.pack . (:) '$' . show $ n
   popArgs (n+1) max
  else return ()
  where _ = n :: Int

cleanupHelper = do
 input <- getInput
 setInput (Special ' ' <| input)
 n <- getArgCount
 maskArgs (1::Int) (n::Int)
 pushUserDef (BS.pack "$@") Nothing
 pushUserDef (BS.pack "$#") Nothing
 pushUserDef (BS.pack "$0") Nothing
 builtinHelper cleanup
 where
  maskArgs b max = helper b where
   helper a = if a > max then don't else do
    pushUserDef (BS.pack . (:) '$' . show $ a) Nothing
    helper (a+1)

pushDefBuiltin :: BuiltinT
pushDefBuiltin state = State.runState helper state where
 helper = {-trace "\n\n\n" $ traceShow state $-} do
  User arg1 <- getDef (BS.pack "$1")
  User arg2 <- getDef (BS.pack "$2")
  pushDef (BS.pack $ toOutputString arg1) (Just $ User $ arg2)
  cleanupHelper
  return Seq.empty

popDefBuiltin :: BuiltinT
popDefBuiltin state = State.runState helper state where
 helper = do
  User arg1 <- getDef (BS.pack "$1")
--  let (Sequence arg1_2):<_ = Seq.viewl arg1_1
  popDef (BS.pack $ toOutputString arg1)
  cleanupHelper
  return Seq.empty

setDefBuiltin :: BuiltinT
setDefBuiltin state = State.runState helper state where
 helper = do
  User arg1 <- getDef (BS.pack "$1")
  User arg2 <- getDef (BS.pack "$2")
  setDef (BS.pack $ toOutputString arg1) (Just $ User $ arg2)
  cleanupHelper
  return Seq.empty

quoteBuiltin :: BuiltinT
quoteBuiltin state = State.runState helper state where
 helper = do
  User arg1 <- getDef (BS.pack "$1")
  cleanupHelper
  return . Seq.singleton . Quote . Seq.singleton . Quote $ arg1

test str = State.runState helper (standardParseState str) where
 helper = do
  tree <- parseExpressionL
  processTree tree

main = do
 args <- System.Environment.getArgs
 let
  str = unwords args
  (result,state) = test str
 putStrLn $ ("input  = " ++ show str)
 putStrLn $ ("result = \"" ++ (toOutputString $ result) ++ "\"")
 putStrLn $ ("state  = \"" ++ show state ++ "\"")

--example1 = "a" ++ "pushDef([[f],[g([[a]],quote($@))]])" ++ "f([[b],[c]])"
example1 = "pushDef([[f],[g([a],$@)]])f([[b],[c]])"
example2 = "pushDef(a,b)a"
example3 = "pushDef(a,b)a(x,y)"
example4 = "pushDef([[a],[b]])quote([a])"

runMain str = System.Environment.withArgs [str] main


