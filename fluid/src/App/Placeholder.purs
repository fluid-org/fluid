module App.Placeholder where

import Prelude

import Effect (Effect)

-- Remove the placeholder shown until the figure loads; the web tests take the page as settled once the
-- placeholder is gone
foreign import figureLoaded :: String -> Effect Unit

-- Replace the placeholder by the error
foreign import figureFailed :: String -> String -> Effect Unit
