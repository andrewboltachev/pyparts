
{-
type Text = String

data Person = Person {
      name :: T.Text
    , age  :: Int
    } deriving (Generic, Eq, Show)

instance ToJSON Person where
    -- No need to provide a toJSON implementation.

    -- For efficiency, we write a simple toEncoding implementation, as
    -- the default version uses toJSON.
    toEncoding = genericToEncoding defaultOptions

instance FromJSON Person
    -- No need to provide a parseJSON implementation.

--decode "{\"foo\":1,\"bar\":2}" :: Maybe (Map String Int)
--
-- x1 = fmap (\x -> Data.Aeson.KeyMap.lookup (Data.Aeson.Key.fromString "body") ((Data.Map.elems x) !! 0)) (decode input :: Maybe (Map String Object))

getData1 :: IO (Maybe Value)
getData1 = do
  fileData <- BL.readFile "/home/andrey/Work/lc/pyparts1.json"
  return $ decode fileData

getData :: IO (Maybe Value)
getData = do
  fileData <- BL.readFile "/home/andrey/Work/lc/pyparts.json"
  return $ decode fileData

t1 a = [show a]

isSubMapOf :: Object -> Value -> Bool
isSubMapOf e (Object a) = (P.all f . KM.toList) e where f (k, v) = KM.lookup k a == (Just v)
isSubMapOf _ _ = False

gather :: (Value -> Bool) -> Value -> [Value]
gather pred x = if (pred x) then [x] else case x :: Value of
            Object a -> P.concat (fmap (gather pred) $ KM.elems a)
            Array a -> P.concat (fmap (gather pred) a)
            _ -> []

-- x1 = (fmap . fmap) (gather (\x -> case x of Object a -> (KM.lookup (K.fromString "type") a) == Just (String "SimpleStatementLine"); _ -> False)) getData
-- (fmap . fmap) ((fmap (\x -> case x of Object a -> KM.lookup (K.fromString "annotation") a; _ -> error "woo")) . (gather (isSubMapOf (KM.fromList [((K.fromString "type"), String "AnnAssign")])))) getData

asArray :: Value -> Maybe [Value]
asArray (Array a) = Just $ Data.Vector.Generic.toList a
asArray _ = Nothing

mHead (x:_) = Just x
mHead _ = Nothing

ff a = do
  a <- asKeyMap a
  a <- KM.lookup (K.fromString "body") a
  a <- asArray a
  return $ P.filter (isSubMapOf (KM.fromList [((K.fromString "type"), String $ T.pack "AnnAssign")])) a

-- fmap (>>= (\x -> case x of Object a -> Just a; _ -> Nothing)) getData
find1 x = do
  x <- asKeyMap x
  x <- KM.lookup (K.fromString "body") x
  x <- asKeyMap x
  x <- KM.lookup (K.fromString "body") x
  x <- asArray x
  --x <- return $ P.concat $ fmap (\x -> if (isSubMapOf (KM.fromList [((K.fromString "type"), String "SimpleStatementLine")])) then x) x
  x <- return $ P.filter (isSubMapOf (KM.fromList [((K.fromString "type"), String $ T.pack "SimpleStatementLine")])) x
  (fmap . fmap) encode $ fmap P.concat $ P.traverse ff x

f1 :: IO (Maybe Value) -> IO ()
f1 theData = do
  d <- theData
  let r = do
            x <- d
            x <- case x of Object a -> Just (KM.toList a); _ -> Nothing
            x <- L.foldl' (\a (k, v) -> (\p -> (++[(k, p)])) <$> (find1 v) <*> a) (Just mempty) x
            return $ P.concat $ fmap (\(k, v) -> (((++"\n") . K.toString) k) ++ ("\t" ++ show v ++ "\n") ++ "\n\n\n") x
  P.putStrLn $ case r of
       Just b -> b
       Nothing -> "Some error perhaps..."
       -}
{-
--matchPattern (MatchArray m) (Array a) = Nothing
matchPattern MatchAny a = MatchSuccess $ MatchAnyResult a
matchPattern (MatchSimpleOr ms) v = fmap MatchSimpleOrResult $ P.foldr f (MatchFailure "or fail") ms
  where f a b = case matchPattern a v of
                     MatchSuccess x -> MatchSuccess x
                     b -> b

-- valueless
matchPattern (MatchApply (MatchOp f) m) v = matchPattern m v >>= f
matchPattern (MatchString m) (String a) = if m == a then MatchSuccess MatchLiteral else NoMatch
matchPattern (MatchNumber m) (Number a) = if m == a then MatchSuccess MatchLiteral else NoMatch
matchPattern (MatchBool m) (Bool a) = if m == a then MatchSuccess MatchLiteral else NoMatch
matchPattern MatchNull Null = MatchSuccess MatchLiteral
-- valued
matchPattern MatchLiteral (String a) = MatchSuccess $ MatchString a
matchPattern MatchLiteral (Number a) = MatchSuccess $ MatchNumber a
matchPattern MatchLiteral (Bool a) = MatchSuccess $ MatchBool a
matchPattern MatchLiteral Null = MatchSuccess $ MatchNull
-- default case
matchPattern _ _ = NoMatch

-- matchPattern (MatchString $ T.pack "abcd") (String $ T.pack "abcd")
-- matchPattern (MatchNumber 11.0) (Number 11.0)
-- matchPattern (MatchBool True) (Bool True)
-- matchPattern MatchNull Null

matchOp = MatchApply . MatchOp

-- pattern -> result -> Either String Value
applyPattern :: MatchPattern -> MatchPattern -> Either String Value
applyPattern (MatchObjectPartial m) (MatchObjectPartialResult m1 m2) = do
  -- <- KM.union m1 (Object a)
  let f a b = a
  mm <- if keys m /= keys m2 then Left "Keys mismatch" else Right $ L.foldl' f (KM.empty) (keys m)
  let m2e err x = case x of
                   Nothing -> Left err
                   Just a -> Right a
  m1' <- (m2e "Map mismatch") $ asKeyMap $ m1
  return $ Object $ KM.union m1' mm

applyPattern (MatchArraySome m) (MatchArraySomeResult a1 a2) = do
  let f a idx = do
          a' <- a
          x <- case P.lookup idx a1 of
                    Just v -> Right v
                    Nothing -> case P.lookup idx a2 of
                                    Nothing -> Left "Index not found"
                                    Just r -> applyPattern m r
          return $ a' ++ [x]
  xx <- (L.foldl' f (Right []) [0..(P.length a1 + P.length a2 - 1)])
  xx <- if P.length xx > 0 then Right xx else Left "..."
  return $ (Array . V.fromList) xx

-- valueless
applyPattern (MatchString m) MatchLiteral = Right (String m)
applyPattern (MatchNumber m) MatchLiteral = Right (Number m)
applyPattern (MatchBool m) MatchLiteral = Right (Bool m)
applyPattern MatchNull MatchLiteral = Right Null

-- valued
applyPattern MatchLiteral (MatchString m) = Right (String m)
applyPattern MatchLiteral (MatchNumber m) = Right (Number m)
applyPattern MatchLiteral (MatchBool m) = Right (Bool m)
applyPattern MatchLiteral MatchNull = Right Null
-- ...
applyPattern _ _ = Left "Unknown error"

matchToValueMinimal :: MatchPattern -> Maybe Value
matchToValueMinimal (MatchObjectPartialResultU m) = fmap Object $ ifNotEmpty =<< L.foldl' f (Just mempty) (keys m)
  where
    ifNotEmpty m = if KM.null m then Nothing else Just m
    f acc k = do
          acc' <- acc
          v <- KM.lookup k m
          return $ case matchToValueMinimal v of
               Nothing -> acc'
               (Just x) -> KM.insert k x acc'
matchToValueMinimal (MatchArraySomeResultU m) = fmap Array $ ifNotEmpty =<< L.foldl' f (Just (V.empty :: V.Vector Value)) arr
  where
    arr = V.fromList $ fmap snd m
    ifNotEmpty m = if V.null m then Nothing else Just m
    f acc v = do
          acc' <- acc
          return $ case matchToValueMinimal v of
               Nothing -> acc'
               (Just x) -> V.snoc acc' x
matchToValueMinimal (MatchString m) = Just (String m)
matchToValueMinimal (MatchNumber m) = Just (Number m)
matchToValueMinimal (MatchBool m) = Just (Bool m)
matchToValueMinimal MatchNull = Just Null
matchToValueMinimal (MatchAnyResult a) = Just a
matchToValueMinimal _ = Nothing

apply1 (MatchObjectPartialResult _ r) = KM.lookup (K.fromString "body") r
apply1 _ = Nothing

apply2 (MatchObjectPartialResult _ r) = KM.lookup (K.fromString "annotation") r
apply2 _ = Nothing

apply3 (MatchArraySomeResult _ r) = do
  (_, m) <- mHead r
  return m
apply3 _ = Nothing

p1 theData = do
  d <- theData
  let v = do
        d' <- d
        d'' <- asKeyMap d'
        let f vv = do
              r <- matchPattern ((MatchApply (MatchOp apply1)) $ MatchObjectPartial
                                (fromList [
                                  (fromString "type", MatchString $ T.pack "ClassDef"),
                                  (fromString "body", (MatchApply (MatchOp apply1)) $ (MatchObjectPartial
                                                      (fromList [
                                                        (fromString "type", MatchString $ T.pack "IndentedBlock"),
                                                        (fromString "body", MatchArraySome $ (MatchApply (MatchOp apply1)) $ (MatchObjectPartial (fromList [
                                                          (fromString "type", MatchString $ T.pack "SimpleStatementLine"),
                                                          (fromString "body", (MatchApply (MatchOp apply3)) $ MatchArraySome (MatchObjectPartial (fromList [
                                                              (fromString "type", MatchString $ T.pack "AnnAssign"),
                                                              (fromString "target", (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Name"),
                                                                                                                   (fromString "value", MatchLiteral)]))),
                                                              (fromString "annotation",
                                                               (MatchApply (MatchOp apply2)) $ (MatchObjectPartial (fromList [(fromString "type", MatchString $ T.pack "Annotation"),
                                                                                              (fromString "annotation",
                                                                                               (MatchMustHave $ MatchSimpleOr
                                                                                               [
                                                                                                (MatchObjectPartial (fromList [
                                                                                                                                (fromString "type", MatchString $ T.pack "Subscript"),
                                                                                                                                (fromString "value", MatchAny),
                                                                                                                                (fromString "slice", MatchAny)
                                                                                                                                ])),
                                                                                                (MatchObjectPartial (fromList [
                                                                                                                                (fromString "type", MatchString $ T.pack "Name"),
                                                                                                                                (fromString "value", MatchLiteral)
                                                                                                                                ]))
                                                                                               ]))])))
                                                            ])))
  
                                                            --(fromString "annotation", )
                                                        ])))
                                                      ])))
                              ])) vv
              r <- return $ resetUnsignificant r
              r <- matchToValueMinimal r
              return r
        return $ (fmap . fmap) f (KM.toList d'')
  return v

catMaybes xs = L.foldl' f mempty xs
  where f a b = case b of
                     Nothing -> a
                     Just x -> a ++ [x]

asString (String x) = Just x
asString _ = Nothing

h1 (Array v) = KM.fromList $ catMaybes $ fmap f (V.toList v)
  where f x = do
                x <- asKeyMap x
                k <- KM.lookup (fromString "target") x
                k <- asKeyMap k
                k <- KM.lookup (fromString "value") k
                k <- asString k
                -- ...
                v <- KM.lookup (fromString "annotation") x
                return $ (fromText k, v)

p2 theData = do
  --v <- (fmap join $ (fmap . fmap) sequenceA $ (fmap . fmap . fmap) sequenceA $ p1 theData) :: IO (Maybe [(Key, Value)]) -- v :: MayBe ...
  v <- (fmap . fmap) catMaybes $ (fmap . fmap . fmap) sequenceA $ p1 theData
  let x = do
            v' <- v -- :: [(Key, Value)]
            let f (k, v) = ((TL.encodeUtf8 . TL.pack) $ K.toString k) <> (TL.encodeUtf8 . TL.pack) "\n\n" <> encode (h1 v) <> (TL.encodeUtf8 . TL.pack) "\n\n"
            return $ BL.concat $ fmap f v' --  $ BL.intersperse ((TL.encodeUtf8 . TL.pack) "\n")
  BL.putStrLn $ case x of
       Nothing -> (TL.encodeUtf8 . TL.pack) "Nothing to see"
       Just y -> y
-- fmap (BL.intersperse $ T.pack " ") $ (fmap . fmap) encode $ fmap catMaybes $ (fmap . fmap) join $ fmap sequenceA $ p1 getData1

{ -
MatchPartialMap
Match...
- }

--match1 = Object (fromList [("body", Object (fromList [("body", v)]))])
--f2 (Object a) = 
--
main = p2 getData
-}
-- grammar
