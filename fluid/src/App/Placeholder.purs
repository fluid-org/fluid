module App.Placeholder where

import Prelude

import Effect (Effect)

-- Remove the placeholder shown until the figure loads; its absence tells the web tests the page has settled
foreign import figureLoaded :: String -> Effect Unit

-- Replace the placeholder by the error
foreign import figureFailed :: String -> String -> Effect Unit
