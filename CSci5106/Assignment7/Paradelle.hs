module Paradelle where

import List 
import Char
import System.IO.Unsafe
import Prelude hiding(getLine)

type Line = [String]
type Stanza = [Line]         
type Poem = [Stanza]

check f = 
  do
    text <- readFile f
    return (resultMessage (is_paradelle text))
  where
    resultMessage r = if r
                      then "The file does contain a paradelle."
                      else "The file does not contain a paradelle."





is_paradelle :: String -> Bool
is_paradelle text = checkLine1 && checkLine2 && checkLine3 && checkLine4
  where
    previousStanzas = (foldr (++) [] (getStanza poem 1)) ++ (foldr (++) [] (getStanza poem 2)) ++ (foldr (++) [] (getStanza poem 3))
    poem = parseIntoStanzas (parseIntoLines text)
    checkLine1 = checkStanza (getStanza poem 1)
    checkLine2 = checkStanza (getStanza poem 2)
    checkLine3 = checkStanza (getStanza poem 3)
    checkLine4 = checkLastStanza (getStanza poem 4) previousStanzas
    


checkStanza :: Stanza -> Bool    
checkStanza stanza = linesEqual (getLine stanza 1) (getLine stanza 2) &&  --first and second are equal
                     linesEqual (getLine stanza 3) (getLine stanza 4) &&  --third and fourth are equal
                     foldr (&&) True (map (wordInSet set) (getLine stanza 5)) && --fifth is composed of 1-4
                     foldr (&&) True (map (wordInSet set) (getLine stanza 6))    --6 is composed of 1-4
                     where
                      set = (getLine stanza 1) ++ (getLine stanza 2) ++ (getLine stanza 3) ++ (getLine stanza 3)
                      wordInSet set word = length (intersect [word] set) > 0
                      
checkLastStanza :: Stanza -> Line -> Bool
checkLastStanza stanza set = foldr (&&) True (map (checkLine set) stanza)
                             where
                              wordInSet set word = length(intersect [word] set) > 0
                              checkLine set line = foldr (&&) True (map (wordInSet set) line)


stanza = head poem
word = ["love"]
set = foldr (++) [] stanza

getStanza :: Poem -> Int -> Stanza
getStanza poem i = if i == 1
                   then head poem
                   else getStanza (tail poem) (i-1)

getLine :: Stanza -> Int -> Line
getLine stanza i = if i == 1 
                   then head stanza
                   else getLine (tail stanza) (i-1)

linesEqual l1 l2 = if length l1 == length l2
                   then foldr (&&) True (map (\(l, r) -> l == r) (zip l1 l2))
                   else False


parseIntoLines :: [Char] -> [Line]
parseIntoLines [] = []
parseIntoLines lines = if head lines == '\n'
                       then parseIntoLines (tail lines)
                       else [words currentLine] ++ parseIntoLines (drop (length currentLine) lines)
                       where
                        currentLine = takeWhile (\x -> x /= '\n') lines
                        
parseIntoStanzas :: [Line] -> Poem
parseIntoStanzas [] = []
parseIntoStanzas poem = if length poem < 6
                        then []
                        else [fst (splitAt 6 poem)] ++ parseIntoStanzas (snd (splitAt 6 poem))


poem = parseIntoStanzas (parseIntoLines s)
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
notPunctuation c = c /= '.' && c /= ',' && c /= '!' && c /= '?' && c /= ';' && c /= ':'
s :: String
s = filter notPunctuation (map toLower (unsafePerformIO ( readFile "paradelle_susan_1.txt")))





