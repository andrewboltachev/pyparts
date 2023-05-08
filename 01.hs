MatchObjectFull (fromList [("body",KeyReq (___)),("default_indent",KeyReq (MatchStringExact "    ")),("default_newline",KeyReq (MatchStringExact "\n")),("encoding",KeyReq (MatchStringExact "utf-8")),("has_trailing_newline",KeyReq (MatchBoolExact False)),("type",KeyReq (MatchStringExact "Module"))])

MatchArrayContextFree (Seq [Or (fromList [
  ("\"1\"",Seq [Char $ MatchStringExact "aaa"]),
  ("\"2\"",Seq [Char $ MatchStringExact "bbb"]),
  ("\"3\"",Seq [Char $ MatchStringExact "ccc"])])])

(MatchObjectFull (fromList [("body",KeyReq (MatchArrayContextFree (Seq [Char (MatchObjectFull (fromList [("semicolon",KeyReq (MatchStringExact "MaybeSentinel.DEFAULT")),("type",KeyReq (MatchStringExact "Expr")),("value",KeyReq (MatchObjectFull (fromList [("type",KeyReq (MatchStringExact "Name")),("value",KeyReq (MatchStringExact "a3"))])))]))]))),("type",KeyReq (MatchStringExact "SimpleStatementLine"))]))
(MatchObjectFull (fromList [("body",KeyReq (MatchArrayContextFree (Seq [Char (MatchObjectFull (fromList [("semicolon",KeyReq (MatchStringExact "MaybeSentinel.DEFAULT")),("type",KeyReq (MatchStringExact "Expr")),("value",KeyReq (MatchObjectFull (fromList [("type",KeyReq (MatchStringExact "Name")),("value",KeyReq (MatchStringExact "a2"))])))]))]))),("type",KeyReq (MatchStringExact "SimpleStatementLine"))]))
(MatchObjectFull (fromList [("body",KeyReq (MatchArrayContextFree (Seq [Char (MatchObjectFull (fromList [("semicolon",KeyReq (MatchStringExact "MaybeSentinel.DEFAULT")),("type",KeyReq (MatchStringExact "Expr")),("value",KeyReq (MatchObjectFull (fromList [("type",KeyReq (MatchStringExact "Name")),("value",KeyReq (MatchStringExact "a1"))])))]))]))),("type",KeyReq (MatchStringExact "SimpleStatementLine"))]))

MatchArrayContextFree (Seq [Or (fromList [("\"1\"",Seq [Char $ MatchStringExact "aaa"]), ("\"2\"",Seq [Char $ MatchStringExact "bbb"]), ("\"3\"",Seq [Char $ MatchStringExact "ccc"])])])

