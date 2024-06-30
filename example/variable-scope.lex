law "Law of Scopes"

type i is int
type s is string

observable event A
    a: i
    b: s

observable event B
    x: s
    y: i

observable event C
    v1: s

observable event D
    v1: i

article "1"

rule "a"
    fix
        v1: i
        v2: s
        v3: s
    whenever
        A(v1, v2)
    oblige
        B(v2, v1)

rule "b"
    whenever
        C(v2)
    except
        rule "a"

rule "c"
    whenever
        D(v1)
    except
        rule "b"

rule "D" 
    whenever
        C(v1)
    oblige
        D(v2)
