module Paradelle where

import List 
import Char
import System.IO.Unsafe
import Prelude hiding(getLine)

check f = 
  do
    text <- readFile f
    return (resultMessage (is_paradelle text))
  where
    resultMessage r = if r
                      then "The file does contain a paradelle."
                      else "The file does not contain a paradelle."

is_paradelle :: String -> Bool
is_paradelle text 
  = False


isPunctuation c = c /= '.' || c /= ',' || c /= '!' || c /= '?' || c /= ';' || c /= ':'

dropPunctuation s = filter isPunctuation s

getLine poem = takeWhile (\x -> x /= '\n') poem


{- 
  Your task is to implement the above function and additional
  functions used by it to solve the assigned problem.

  In doing so, you should determine a way to functionally decompose
  the problem.  This will involve writing and using some additional
  functions but should also make use of providing names to
  intermediate values.

  In Haskell, this can be done using a "where" clause.  It serves the
  same purpose as "let" expressions but the values defined come after
  the expression in which they are used.

  An example is provided above in "check" and below in an example of
  allEven: 
-}

allEven xs = foldr f z xs
  where
    z = True
    f nextNum remaining = even nextNum  &&  remaining

{-
  You might, for example, use a where clause to bind the name
  "has_24_lines" to a boolean value that is true if the text has 24
  non-blank lines.

  By providing illustrative names for intermediate values in this way,
  your functional decomposition is made clear and easy to read.

  You will be assessed on the functional correctness of your code as
  well as how easy it is to read and understand.  Thus you should
  spend some time cleaning up your code as you develop it.

  You may want some of your helper functions to NOT be placed in a
  where clause of some other function.  If they are defined at the
  "top-level" then they can be called from the interpreter and you can
  more easily experiment with them.

  You might also find it helpful to store the contents of a file in a
  named string so that you can pass it to your helper functions while
  experimenting with your helper functions.  To do this, use the
  following:
-}
s :: String
s = map toLower (unsafePerformIO ( readFile "paradelle_susan_1.txt"))
