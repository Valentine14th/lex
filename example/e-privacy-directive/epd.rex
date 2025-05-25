refine epd

refine type person is string

observable event userGivesConsent
    """ person {s} gives consent to receive
    automated marketing communication from
    person {r} """
    r: person
    s: person

observable event userWithdrawsConsent
    """ person {s} withdraws consent to receive
    automated marketing communication from
    person {r} """
    r: person
    s: person

rule "refine marketing consent"
    whenever
        ONCE userGivesConsent(r, s)
        (NOT userWithdrawsConsent(r, s)) SINCE userGivesConsent(r, s)
    refine
        marketingConsent(r, s)

assume true objectToSimilarEmailMarketing
