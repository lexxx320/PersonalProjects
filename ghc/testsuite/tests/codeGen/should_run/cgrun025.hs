-- !!! test various I/O Requests
--
--
import IO
import System
import Debug.Trace (trace)
import Text.Regex
import Maybe

main = do
    prog <- getProgName
    let Just (name:_) = matchRegex (mkRegex ".*(cg025)") prog
    hPutStr stderr (shows name "\n")
    args <- getArgs
    hPutStr stderr (shows args "\n")
    path <- getEnv "PATH"
    hPutStr stderr ("GOT PATH\n")
    stdin_txt <- getContents
    putStr stdin_txt
    file_cts <- readFile (head args)
    hPutStr  stderr file_cts
    trace "hello, trace" $
      catch (getEnv "__WURBLE__" >> return ()) (\ e -> error "hello, error")
