module Test.Specs.Dependence where

import App.Util.Selector (select)
import DataType (cPair, f_snd)
import Test.Util (DepSpec)

dep_cases :: Array DepSpec
dep_cases =
   [ { file: "var.fld", δv: \_ -> select, expect: "x: ⸨[⸨1⸩, ⸨2⸩]⸩" }
   , { file: "cond.fld", δv: \_ -> select, expect: "b: ⟪True⟫\ny: ⸨1⸩\nz: 2" }
   , { file: "match_fallthrough.fld", δv: \_ -> select, expect: "v: ⟪Bar()⟫\nw: ⸨5⸩" }
   , { file: "early_return.fld", δv: \_ -> select, expect: "a: 1\nb: ⸨2⸩\nc: ⟪False⟫" }
   , { file: "attribute.fld", δv: \_ -> select, expect: "p: ⟪P(⸨1⸩, 2)⟫" }
   , { file: "subscript.fld", δv: \_ -> select, expect: "i: ⟪1⟫\nxs: ⟪[3, ⸨4⸩, 5]⟫" }
   , { file: "filter.fld", δv: \_ -> select, expect: "n: ⟪5⟫\nxs: ⟪[⸨8⸩, ⟪4⟫, ⸨7⸩, ⟪3⟫]⟫" }
   , { file: "closure.fld", δv: \_ -> select, expect: "a: ⸨1⸩\nb: ⸨2⸩" }
   , { file: "partial.fld", δv: \_ -> select, expect: "a: ⸨1⸩\nb: ⸨2⸩" }
   , { file: "len.fld", δv: \_ -> select, expect: "len: ⟪len⟫\nxs: ⸨[1, 2]⸩" }
   , { file: "dict_lookup.fld", δv: \_ -> select, expect: "d: ⟪{⟪\"a\"⟫: ⸨1⸩, \"b\": 2}⟫" }
   , { file: "seq.fld", δv: \arg -> arg cPair f_snd select, expect: "a: 1\nb: 2\nc: ⟪True⟫\nd: ⸨4⸩" }
   ]
