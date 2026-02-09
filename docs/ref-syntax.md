# MetaPost Syntax Reference

Extracted from `mpman.tex` and `mpman-app-refman.tex`. Complete BNF for
the MetaPost language.

## Expression Grammar

```
atom → variable | argument
     | <number or fraction>
     | <internal variable>
     | ( expression )
     | begingroup <statement list> expression endgroup
     | <nullary op>
     | btex <typesetting commands> etex
     | <pseudo function>

primary → atom
        | ( <numeric expr> , <numeric expr> )                  -- pair
        | ( <numeric expr> , <numeric expr> , <numeric expr> ) -- color
        | <of operator> expression of primary
        | <unary op> primary
        | str suffix
        | z suffix                                             -- (x.sfx, y.sfx)
        | <numeric atom> [ expression , expression ]           -- mediation
        | <scalar multiplication op> primary                   -- +/- prefix

secondary → primary
          | secondary <primary binop> primary
          | secondary <transformer>

tertiary → secondary
         | tertiary <secondary binop> secondary

subexpression → tertiary
              | <path expression> <path join> <path knot>

expression → subexpression
           | expression <tertiary binop> tertiary
           | <path subexpression> <direction specifier>
           | <path subexpression> <path join> cycle
```

## Operator Classification

```
nullary op → false | normaldeviate | nullpen | nullpicture
           | pencircle | true | whatever

unary op → <type>
         | abs | angle | arclength | ASCII | bbox | blackpart | bluepart
         | bot | bounded | ceiling | center | char | clipped | colormodel
         | cosd | cyanpart | cycle | dashpart | decimal | dir | floor
         | filled | fontpart | fontsize | greenpart | greypart | hex
         | inverse | known | length | lft | llcorner | lrcorner
         | magentapart | makepath | makepen | mexp | mlog | not | oct
         | odd | pathpart | penpart | readfrom | redpart | reverse
         | round | rt | sind | sqrt | stroked | textpart | textual
         | top | ulcorner | uniformdeviate | unitvector | unknown
         | urcorner | xpart | xxpart | xypart | yellowpart | ypart
         | yxpart | yypart

type → boolean | cmykcolor | color | numeric | pair
     | path | pen | picture | rgbcolor | string | transform

primary binop → * | / | ** | and | dotprod | div | infont | mod

secondary binop → + | - | ++ | +-+ | or
                | intersectionpoint | intersectiontimes

tertiary binop → & | < | <= | <> | = | > | >= | cutafter | cutbefore

of operator → arctime | direction | directiontime | directionpoint
            | glyph | penoffset | point | postcontrol | precontrol
            | subpath | substring

transformer → rotated <numeric primary>
            | scaled <numeric primary>
            | shifted <pair primary>
            | slanted <numeric primary>
            | transformed <transform primary>
            | xscaled <numeric primary>
            | yscaled <numeric primary>
            | zscaled <pair primary>
            | reflectedabout( <pair expr>, <pair expr> )
            | rotatedaround( <pair expr>, <numeric expr> )
```

## Path Syntax

```
path knot → tertiary

path join → --
          | <direction specifier> <basic path join> <direction specifier>

direction specifier → <empty>
                    | { curl <numeric expression> }
                    | { <pair expression> }
                    | { <numeric expression> , <numeric expression> }

basic path join → ..
                | ...                               -- macro: inflection-free
                | .. <tension> ..
                | .. <controls> ..

tension → tension <numeric primary>
        | tension <numeric primary> and <numeric primary>

controls → controls <pair primary>
         | controls <pair primary> and <pair primary>
```

## Numeric Primaries (special rules)

```
numeric primary → numeric atom
               | <numeric atom> [ <numeric expr>, <numeric expr> ]
               | <of operator> expression of primary
               | <unary op> primary

numeric atom → <numeric variable>
             | <number or fraction>
             | ( <numeric expression> )
             | <numeric nullary op>

number or fraction → <number> / <number>       -- fraction literal 2/3
                   | <number>                   -- plain number

scalar multiplication op → + | -
                         | <number or fraction not followed by addop+number>
```

**Key rule**: `2/3` is a single atom (fraction), but `(1+1)/3` parses as
division. So `sqrt 2/3` = √(2/3) but `sqrt(1+1)/3` = (√2)/3.

## Variable Syntax

```
variable → tag suffix
suffix → <empty> | suffix subscript | suffix tag
subscript → <number> | [ <numeric expression> ]
```

Tags are symbolic tokens with no predefined meaning. Period between tags
is ignored (acts as separator): `a.b` = tokens `a` and `b`.

## Program Structure

```
program → <statement list> end

statement list → <empty> | <statement list> ; statement

statement → <empty>
          | equation | assignment
          | declaration | macro definition
          | compound | pseudo procedure
          | command

compound → begingroup <statement list> endgroup
         | beginfig( <numeric expr> ); <statement list> ; endfig

equation → expression = <right-hand side>
assignment → variable := <right-hand side>
           | <internal variable> := <right-hand side>
right-hand side → expression | equation | assignment

declaration → type <declaration list>
declaration list → <generic variable> | <declaration list>, <generic variable>
generic variable → <symbolic token> <generic suffix>
generic suffix → <empty> | <generic suffix> tag | <generic suffix> []
```

## Macro Definitions

```
macro definition → <macro heading> = <replacement text> enddef

macro heading → def <symbolic token> <delimited part> <undelimited part>
             | vardef <generic variable> <delimited part> <undelimited part>
             | vardef <generic variable> @# <delimited part> <undelimited part>
             | <binary def> <parameter> <symbolic token> <parameter>

delimited part → <empty>
               | <delimited part> ( <parameter type> <parameter tokens> )

parameter type → expr | suffix | text

undelimited part → <empty>
                 | <parameter type> <parameter>
                 | <precedence level> <parameter>
                 | expr <parameter> of <parameter>

precedence level → primary | secondary | tertiary
binary def → primarydef | secondarydef | tertiarydef
```

## Conditionals and Loops

```
if test → if <boolean expr> : <balanced tokens> <alternatives> fi
alternatives → <empty>
             | else : <balanced tokens>
             | elseif <boolean expr> : <balanced tokens> <alternatives>

loop → <loop header> : <loop text> endfor
loop header → for <sym token> = <progression>
            | for <sym token> = <for list>
            | for <sym token> within <picture expression>
            | forsuffixes <sym token> = <suffix list>
            | forever

progression → <numeric expr> upto <numeric expr>
            | <numeric expr> downto <numeric expr>
            | <numeric expr> step <numeric expr> until <numeric expr>
```

## Drawing Commands Syntax

```
addto command →
    addto <picture variable> also <picture expr> <option list>
  | addto <picture variable> contour <path expr> <option list>
  | addto <picture variable> doublepath <path expr> <option list>

option list → <empty> | <drawing option> <option list>

drawing option → withcolor <color expr>
              | withrgbcolor <rgbcolor expr>
              | withcmykcolor <cmykcolor expr>
              | withgreyscale <numeric expr>
              | withoutcolor
              | withprescript <string expr>
              | withpostscript <string expr>
              | withpen <pen expr>
              | dashed <picture expr>
```

## Character Classes (Tokenization)

Characters on the same row merge into a single symbolic token:

```
Row 1: A-Z _ a-z         (letters + underscore)
Row 2: : < = >           
Row 3: # & @ $            
Row 4: / * \              
Row 5: + -                
Row 6: ! ?                
Row 7: ' `                
Row 8: ^ ~                
Row 9: { }                
Row 10: [                 (self only)
Row 11: ]                 (self only)
```

Loners (always separate tokens): `, ; ( )`

Period: `..` and `...` are symbolic tokens. Single `.` is ignored
(separator). `.5` starts a number.

`%` starts a comment to end of line.
