law "OR"

article "336" 

type person
type kuendigung
type persoenliche_eigenschaft
type taetigkeit
type betrieb
type recht
type arbeitsvertrag
type anspruch
type pflicht

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

observable event Ausueben
    """Partei {p} uebt das Recht {r} aus."""
    p : person
    r : recht

observable predicate Verfassungsmaessig
    """Das Recht {r} ist verfassungsmaessig."""
    r : recht

observable event PflichtVerletzung
    """Die Ausuebung des Rechts {r} verletzt die Pflicht {a}."""
    r : recht
    a : arbeitsvertrag

observable event BeabsichtigtAnspruechVereitelung
    """Durch die Kuendigung {k} wird bezweckt, die Entstehung von Anspruechen der {p} 
       aus dem Arbeitsverhältnis {a} zu vereiteln."""
    k : kuendigung
    p : person
    a : arbeitsvertrag

observable event GeltendMachen
    """Partei {p} macht den Anspruch {an} nach Treu und Glaube aus dem Arbeitsverhältnis {a} geltend."""
    p : person
    an : anspruch
    a : arbeitsvertrag

observable predicate AnspruchZusammenhang
    """Das Geltendmachen des Anspruches {an} ist der Grund für die Kuendigung {k}."""
    an : anspruch
    k : kuendigung

observable event Erfuellt
    """Partei {p} leistet schweizerischen obligatorischen Militaer- oder Schutzdienst 
       oder schweizerischen Zivildienst oder erfuellt eine nicht freiwillig uebernommene 
       gesetzliche Pflicht."""
    p : person
    pf : pflicht

observable predicate PflichtZusammenhang
    """Das Erfuellen der Pflicht {pf} ist der Grund fuer die Kuendigung {k}."""
    pf : pflicht
    k : kuendigung

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

point "b"

rule "verfassungsmaessig"
    whenever
        Kuendigen(k, p1, p2)
        Ausueben(p2, r)
        Verfassungsmaessig(r)
    constitute
        Missbrauechlich(k)

rule "verfassungsmaessig_ausnahme_1"
    whenever
        PflichtVerletzung(r, a)
    except
        rule "verfassungsmaessig_ausnahme_1"

rule "verfassungsmaessig_ausnahme_2"
    whenever
        StoertZusammenarbeit(e, b)
    except
        rule "verfassungsmaessig_ausnahme_2"

point "c" 

rule "vereitelung"
    whenever
        BeabsichtigtAnspruechVereitelung(k, p2, a)
    constitute
        Missbrauechlich(k)

point "d"

rule "ansprueche"
    whenever
        ONCE GeltendMachen(p2, a, an)
        AnspruchZusammenhang(an, k)
    constitute
        Missbrauechlich(k)

point "e"

rule "pflicht"
    whenever
        ONCE Erfuellt(p2, pf)
        PflichtZusammenhang(pf, k)
    constitute
        Missbrauechlich(k)

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
    transparently enforceable causing effects

paragraph "2"

paragraph "3"

article "336b"

paragraph "1"

paragraph "2"
