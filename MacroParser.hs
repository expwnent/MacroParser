
--module MacroParser

import Control.Applicative ((<|>))
import Control.Monad.Trans.Class
import qualified Control.Monad.State.Strict as State
import Control.Monad.State.Strict (StateT)
import qualified Control.Monad.Trans.Error as Error
import Control.Monad.Trans.Error (ErrorT)
--import qualified Control.Monad.Exception as Except
--import Control.Monad.Exception(MonadException, 
import qualified Control.Monad.Trans.Identity as Identity
import qualified Data.ByteString.Char8 as ByteString
import qualified Data.ByteString.Char8 as BS
import Data.ByteString.Char8 (ByteString, pack, unpack)
import Data.Either
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import qualified Data.Sequence as Sequence
import Data.Sequence (Seq, (><), (|>), (<|))
import qualified Data.Trie as Trie
import qualified Data.Trie.Internal as TrieInternal
import Data.Trie (Trie)
import Data.Word

type MacroMap = Map String [String]
type TrieSet = Trie ()
type MacroNames = Trie [ByteString]
--type ParseState = (MacroMap, MacroNames)
type Output = Sequence.Seq ByteString
type ParseState = MacroNames

{-
data ParseState = ParseState {
--  macroMap :: MacroMap
 macroNames :: MacroNames
 ,output :: Output
} deriving (Show,Eq)
-}

toWord8 c = BS.head $ BS.singleton c

emptyState = Trie.empty --ParseState Trie.empty Sequence.empty

getState :: Monad m => StateT ParseState m ParseState
getState = State.get

setState :: Monad m => ParseState -> StateT ParseState m ()
setState s = State.put s

getMacroNames :: Monad m => StateT ParseState m MacroNames
--getMacroNames = State.get >>= return . macroNames
getMacroNames = getState

setMacroNames :: Monad m => MacroNames -> StateT ParseState m ()
--setMacroNames names = do
-- old <- getState
-- setState $ old { macroNames = names }
setMacroNames = setState

--------------------------------------------------
------------parsers start here
--------------------------------------------------
parseString :: Monad m => ByteString -> ErrorT String (StateT ParseState m) ByteString
parseString str = do
 let input = ByteString.pack "input"
 _pushDef input (str)
 result <- processInput
 _popDef input
 return result

processInput :: Monad m => ErrorT String (StateT ParseState m) ByteString
processInput = parseMany parseSomething

parseSomething :: Monad m => ErrorT String (StateT ParseState m) ByteString
parseSomething = parseAny $ (map (\x -> tryParse $ x) [parseQuotedString, parseMacroName]) ++ [tryParse popInput]

parseQuotedString :: Monad m => ErrorT String (StateT ParseState m) ByteString
parseQuotedString = do
 parseLiteral' (pack "[")
 helper 1
 where
  helper :: Monad m' => Int -> ErrorT String (StateT ParseState m') ByteString
  helper 0 = return ByteString.empty
  helper n = do
   c <- popInput
   if c == pack "[" then
    helper (n+1) >>= return . (BS.append c)
   else if c == pack "]" then
    let dumb = if n>1 then c else BS.empty in dumb `seq` helper (n-1) >>= return . (ByteString.append dumb)
   else if c == pack "\\" then do
    c' <- popInput
    helper n >>= return . (ByteString.append c')
   else helper n >>= return . (ByteString.append c)

_temporaryPush term def = do
 _pushDef term def
 _pushDef (pack "pushed") (quote term)

parseMacroName :: Monad m => ErrorT String (StateT ParseState m) ByteString
parseMacroName = do
 macroNames <- lift $ getMacroNames
 macro <- helper macroNames
 expansion <- _getDef' macro
 let
  preamble = do
   _pushDef (pack "pushed") (pack "done")
   _temporaryPush (pack "$0") macro
   _temporaryPush (pack "$#") (pack "0")
   _temporaryPush (pack "$@") (pack "")
  cleanup = do
   top' <- _peekPopDef (pack "pushed")
   top <- maybeToError top'
   if top == pack "done" || top == quote (pack "done") then return ()
   else do
    _popDef top
    cleanup
 preamble
 maybeParse (_parseMacroArguments macro)
 expansionParsed <- parseString (expansion)
 cleanup
 return expansionParsed
 where
  helper names
   | Trie.null names = Error.throwError "Not a macro name."
   | Trie.member ByteString.empty names =
      Error.catchError (tryParse (helper (Trie.delete ByteString.empty names))) $ \_ -> return BS.empty
   | otherwise = do
      c <- popInput
      helper (trieReducer c names) >>= return . (BS.append c)

_parseMacroArguments :: Monad m => ByteString -> ErrorT String (StateT ParseState m) ()
_parseMacroArguments macro = do
 parseLiteral' (pack "(")
 allArgs <- parseArgs
 parseLiteral' (pack ")")
 _setDef (pack "$@") allArgs
 return ()
 where
  preparseArgument :: Monad m => ErrorT String (StateT ParseState m) ByteString
  preparseArgument = do
   c <- peekInput
   if c == pack "," || c == pack ")" then
    return BS.empty
   else do
    r1 <- parseSomething
    r2 <- preparseArgument
    return (BS.append r1 r2)
  parseArgs :: Monad m => ErrorT String (StateT ParseState m) ByteString
  parseArgs = do
   c <- _getDef (pack "input")
   if Maybe.isNothing c || BS.head (Maybe.fromJust c) == toWord8 ')' then
    return BS.empty
   else do
    argument <- preparseArgument
    c' <- popInput
    n' <- _getDefNull (pack "$#")
    let
     n :: Int
     n = read $ unpack n'
    _temporaryPush (pack ("$" ++ show (1+n))) (quote argument)
    _setDef (pack "$#") (pack $ show (1+n))
    if c' == pack "," then do
     result <- parseArgs
     return $ BS.concat [(quote argument), pack ",", result]
    else
     return $ (quote argument)

--the exception to the evaluate the args before calling rule
parseLiteral' :: Monad m => ByteString -> ErrorT String (StateT ParseState m) ByteString
parseLiteral' arg
 | BS.null arg = return BS.empty
 | otherwise = do
    b <- popInput
    let a = BS.singleton $ BS.head arg
    if a /= b then Error.throwError "parseLiteral' mismatch"
    else parseLiteral' (BS.tail arg) >>= return . BS.append a

maybeParse :: Monad m => ErrorT String (StateT ParseState m) a -> ErrorT String (StateT ParseState m) (Maybe a)
maybeParse operation = Error.catchError (operation >>= return . Just) (\_ -> return Nothing)

tryParse :: Monad m => ErrorT String (StateT ParseState m) a -> ErrorT String (StateT ParseState m) a
tryParse operation = do
 state <- lift $ getState
 Error.catchError operation $ \e -> do
  lift $ setState state
  Error.throwError e

parseAny :: Monad m => [ErrorT String m a] -> ErrorT String m a
parseAny (a:aL) = do
 Error.catchError a (\_ -> parseAny aL)
parseAny [] = Error.throwError "parseAny ran out of options"

parseMany :: Monad m => ErrorT String (StateT ParseState m) ByteString -> ErrorT String (StateT ParseState m) ByteString
parseMany operation = do
 r1 <- operation
 Error.catchError (parseMany operation >>= \r2 -> return $ BS.append r1 r2) (\_ -> return r1)
{-
parseMany operation = do
 let
  helper = do
   r1 <- operation
   r2 <- (parseMany operation)
   return (BS.append r1 r2)
 Error.catchError ({-tryParse-} helper) $ \_ -> return BS.empty
-}

trieReducer :: ByteString -> Trie a -> Trie a
trieReducer prefix names = TrieInternal.lookupBy_ (\a tr -> if Maybe.isJust a then Trie.insert ByteString.empty (Maybe.fromJust a) tr else tr) Trie.empty id prefix names

-----------------------------------------
-------end of parsers
-----------------------------------------

maybeHead :: [a] -> Maybe a
maybeHead (a:_) = Just a
maybeHead [] = Nothing

maybeHeadCdr (a:aL) = Just (a,aL)
maybeHeadCdr [] = Nothing

maybeToError :: Monad m => Maybe a -> ErrorT String m a
maybeToError (Just a) = return a
maybeToError Nothing = Error.throwError "maybeToError"

errorToMaybe :: Monad m => ErrorT String m a -> m (Maybe a)
errorToMaybe err = do
 result <- Error.runErrorT
   (Error.catchError 
     (err >>= \a -> return (Just a))
     (\_ -> return Nothing))
 return (unEither result)

unEither :: Either a b -> b
unEither (Right b) = b

getDefStack' :: Monad m => ByteString -> ErrorT String (StateT ParseState m) [ByteString]
getDefStack' var = do
 table <- lift getMacroNames
 Trie.lookupBy (\val _ -> maybeToError val) var table

unmaybe (Just _) x y = x
unmaybe Nothing x y = y

getDefStack :: Monad m => ByteString -> StateT ParseState m [ByteString]
getDefStack var = do
 table <- getMacroNames
 return $ Trie.lookupBy (\val _ -> if Maybe.isNothing val then [] else let Just v2 = val in v2) var table

getDef' :: Monad m => ByteString -> ErrorT String (StateT ParseState m) ByteString
getDef' var' = do
 var <- parseString var'
 _getDef' var
_getDef' :: Monad m => ByteString -> ErrorT String (StateT ParseState m) ByteString
_getDef' var = do
 table <- lift getMacroNames
 maybeToError $ Trie.lookupBy (\v _ -> if Maybe.isNothing v then Nothing else let Just v' = v in if null v' then Nothing else let v'' = head v' in if BS.null v'' then Nothing else Just v'') var table

getDef :: Monad m => ByteString -> ErrorT String (StateT ParseState m) (Maybe ByteString)
getDef var' = do
 var <- parseString var'
 _getDef var
_getDef :: Monad m => ByteString -> ErrorT String (StateT ParseState m) (Maybe ByteString)
_getDef var = do
 table <- lift $ getMacroNames
 return $ Trie.lookupBy (\val _ -> if Maybe.isNothing val then Nothing else let Just val' = val in if null val' then Nothing else let val'' = head val' in if BS.null val'' then Nothing else Just val'') var table

getDefNull :: Monad m => ByteString -> ErrorT String (StateT ParseState m) ByteString
getDefNull var' = do
 var <- parseString var'
 _getDefNull var
_getDefNull :: Monad m => ByteString -> ErrorT String (StateT ParseState m) ByteString
_getDefNull var = do
 table <- lift $ getMacroNames
 return $ Trie.lookupBy (\val _ -> if Maybe.isNothing val then BS.empty else let Just val2 = val in if null val2 then BS.empty else let val3 = head val2 in val3) var table

pushDef :: Monad m => ByteString -> ByteString -> ErrorT String (StateT ParseState m) ()
pushDef var' def' = do
 var <- parseString var'
 def <- parseString def'
 _pushDef var def
_pushDef :: Monad m => ByteString -> ByteString -> ErrorT String (StateT ParseState m) ()
_pushDef var def = lift $ do
 table <- getMacroNames
 setMacroNames $ Trie.alterBy (\_ new val -> if Maybe.isNothing val then Just new else let Just val2 = val in Just (new ++ val2)) var [def] table

peekPopDef :: Monad m => ByteString -> ErrorT String (StateT ParseState m) (Maybe ByteString)
peekPopDef var' = do
 var <- parseString var'
 _peekPopDef var
_peekPopDef :: Monad m => ByteString -> ErrorT String (StateT ParseState m) (Maybe ByteString)
_peekPopDef var = do
 table <- lift getMacroNames
 let result = Trie.lookupBy (\v _ -> v) var table
 _popDef var
 return (if Maybe.isNothing result then Nothing else let Just r2 = result in if null r2 then Nothing else let r3 = head r2 in if BS.null r3 then Nothing else Just r3)

popDef :: Monad m => ByteString -> ErrorT String (StateT ParseState m) ()
popDef var' = do
 var <- parseString var'
 _popDef var
_popDef :: Monad m => ByteString -> ErrorT String (StateT ParseState m) ()
_popDef var = lift $ do
 table <- getMacroNames
 let
  isSingleton asdf = BS.length asdf <= 1
  result = Trie.alterBy (\ _ _ val -> if Maybe.isNothing val then Nothing else let Just val2 = val in if null val2 then Nothing else let val3 = tail val2 in if null val3 then Nothing else Just val3) var [] table
 setMacroNames result

setDef :: Monad m => ByteString -> ByteString -> ErrorT String (StateT ParseState m) ()
setDef var' def' = do
 var <- parseString var'
 def <- parseString def'
 _setDef var def
_setDef :: Monad m => ByteString -> ByteString -> ErrorT String (StateT ParseState m) ()
_setDef var def = do
 _popDef var
 _pushDef var def

don't :: Monad m => m ()
don't = return ()

peekInput :: Monad m => ErrorT String (StateT ParseState m) ByteString
peekInput = do
 table <- lift getMacroNames
 maybeToError $ Trie.lookupBy (\val _ -> if Maybe.isNothing val then Nothing else let Just v2 = val in if null v2 then Nothing else let v3 = head v2 in if BS.null v3 then Nothing else let v4 = BS.singleton (BS.head v3) in Just v4) (pack "input") table

popInput :: Monad m => ErrorT String (StateT ParseState m) ByteString
popInput = do
 result <- peekInput
 table <- lift getMacroNames
 lift $ setMacroNames $ Trie.alterBy (\_ _ v -> if Maybe.isNothing v then Nothing else let Just v2 = v in if null v2 then Nothing else let v3 = head v2 in if BS.null v3 then Nothing else if BS.null (BS.tail v3) then Nothing else Just ((BS.tail v3):tail v2)) (ByteString.pack "input") [] table
 return result

quote :: ByteString -> ByteString
quote str = BS.append (BS.pack "[") (BS.append str (BS.pack "]"))

{-
main = do
  putStrLn "Hello";
  let operation =	setDef (quote (pack "input")) (quote (pack "abaab")) >>
	 		setDef (quote (pack "ab")) (quote BS.empty) >>
	 		setDef (quote (pack "ac")) (quote BS.empty) >>
	 		setDef (quote (pack "abaa")) (quote BS.empty) >>
	 		processInput;
--  let dooom = State.evalState (Error.runErrorT operation) emptyState ;
  doom <- State.evalStateT (Error.runErrorT operation) emptyState;
	 putStrLn ("sdf = " ++ (show doom));
-}

{-
--	putStrLn $ show $ Trie.member ByteString.empty (Trie.singleton ByteString.empty [])
 let
  trie = Trie.fromList $ flip zip (repeat ()) $ map ByteString.pack ["a","ab","aaa","aac","d"]
 putStrLn $ show $ trie
 putStrLn $ show $ trieReducer (ByteString.pack "") $ trie
 putStrLn $ show $ trieReducer (ByteString.pack "a") $ trie
 putStrLn $ show $ trieReducer (ByteString.pack "aa") $ trie
 putStrLn $ show $ trieReducer (ByteString.pack "aab") $ trie
-}
main = do
 let
--  experiment :: Monad m' => ErrorT String (StateT ParseState m') ByteString
  experiment = do
   setDef (quote $ pack "input")  ({-quote-} (pack "Once there asdf was a qwertydoom[asdf]!! func(123,456)"))
   setDef (quote $ pack "asdf") (quote (pack "[qwerty]qwerty"))
   setDef (quote $ pack "qwerty") (quote (pack "doom"))
   setDef (quote $ pack "func") (quote (pack "$2 $1"))
   processInput
 putStrLn $ show $ State.runState (Error.runErrorT experiment) emptyState
 putStrLn $ "The end."

