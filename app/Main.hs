module Main where

import SocialNetwork.Db (withDb, initDb)
import SocialNetwork.Server (runServer)

main :: IO ()
main = withDb "social-network.db" $ \conn -> do
  initDb conn
  putStrLn "Initialized database"
  runServer 3000 conn
