{-# LANGUAGE OverloadedStrings #-}
module Logging where

import qualified Data.Text as T
import Data.Time.Clock
-- NOTE: System.Clock makes it difficult to build a static binary

elapsed :: UTCTime -> UTCTime -> T.Text -> T.Text
elapsed start end action =
  "  [" <> action <> " took " <> T.pack (show diff) <> " seconds]"
  where
    diff = realToFrac (diffUTCTime end start) :: Double
