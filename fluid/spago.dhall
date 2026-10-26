{-
Welcome to a Spago project!
You can edit this file as you like.
-}
let baseSources =
      [ "src/**/*.purs"
      , "test/**/*.purs"
      , "config/*.purs"
      ]

in  { name = ""
    , dependencies =
      [ "aff"
      , "affjax"
      , "affjax-web"
      , "argonaut-codecs"
      , "argonaut-core"
      , "arrays"
      , "bifunctors"
      , "console"
      , "control"
      , "debug"
      , "effect"
      , "either"
      , "enums"
      , "exceptions"
      , "filterable"
      , "foldable-traversable"
      , "foreign"
      , "foreign-object"
      , "functions"
      , "functors"
      , "graphs"
      , "http-methods"
      , "identity"
      , "integers"
      , "lazy"
      , "lists"
      , "maybe"
      , "newtype"
      , "node-buffer"
      , "node-fs"
      , "node-process"
      , "nonempty"
      , "nullable"
      , "numbers"
      , "optparse"
      , "ordered-collections"
      , "parsing"
      , "partial"
      , "prelude"
      , "profunctor"
      , "st"
      , "strings"
      , "tailrec"
      , "transformers"
      , "tuples"
      , "unfoldable"
      , "unicode"
      , "unsafe-coerce"
      , "web-events"
      ]
    , packages = ./packages.dhall
    , baseSources
    , sources = baseSources # [ "config/dev/**/*.purs" ]
    , backend = "npx purs-backend-es build"
    }
