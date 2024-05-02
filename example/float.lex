law "GDPR"

type id is int
type value is float

note "This is a test file"

internal event cause
    j: id

observable event action
    i: id
    f: value

chapter "II"
article "5"
paragraph "1"
point "a"
rule
    whenever
        action(a, 0.2)
        action(b, .2)
        action(c, 2.)
    oblige
        cause(a)
        cause(b)
        cause(c)
enforceable suppressing PersonalDataProcessing 
