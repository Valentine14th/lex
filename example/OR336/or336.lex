law "OR"

article "336" 

type person
type kuendigung
type persoenliche_eigenschaft
type taetigkeit
type betrieb

observable event Kuendigen
    """Die Kuendigung {k} wird von Partei {p1} gegenüber Partei {p2} eingeleitet."""
    k : kuendigung
    p1 : person
    p2 : person

internal event Missbrauechlich
    """Die Kuendigung {k} ist missbraeuchlich."""
    k : kuendigung

observable event Diskriminerend
    """Der Grund der Kuendigung {k} stützt sich auf die persoenliche Eigenschaft {e}."""
    k : kuendigung
    e : persoenliche_eigenschaft

observable event Zusammenhang
    """Es besteht ein Zusammenhang zwischen der persoenlichen Eigenschaft {e} und der beruflichen Taetigkeit {t}."""
    e : persoenliche_eigenschaft
    t : taetigkeit

observable event StoertZusammenarbeit
    """Die persoenliche Eigenschaft {e} stoert die betriebliche Zusammenarbeit im {b}."""
    e : persoenliche_eigenschaft
    b : betrieb

causable event Entschaedigung
    """Partei {p1} muss Partei {p2} eine Entschaedigung zahlen."""
    p1 : person
    p2 : person
    

paragraph "1"

point "a"

rule "diskriminierungskuendigung"
    whenever
        Diskriminerend(k, e)
    constitute
        Missbrauechlich(k)

rule "diskriminierungkuendigung_ausnahme_1"
    whenever
        Zusammenhang(e, t)
    except
        rule "diskriminierungskuendigung"

rule "diskriminierungkuendigung_ausnahme_2"
    whenever
        StoertZusammenarbeit(e, b)
    except
        rule "diskriminierungskuendigung"

paragraph "2"

paragraph "3"

article "336a"

paragraph "1"

rule
    whenever
        Kuendigen(k, p1, p2)
        Missbrauechlich(k)
    oblige
        Entschaedigung(p1, p2)
    transparently enforceable causing Entschaedigung

paragraph "2"

paragraph "3"

article "336b"

paragraph "1"

paragraph "2"