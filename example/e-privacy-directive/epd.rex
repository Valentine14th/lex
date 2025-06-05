refine epd

refine type person is string

observable event userGivesConsent
    """ person {s} gives consent to receive automated marketing communication from person {r} """
    r: person
    s: person

observable event userWithdrawsConsent
    """ person {s} withdraws consent to receive automated marketing communication from person {r} """
    r: person
    s: person

observable event over18
    """ person {r} is over 18 years old """
    r: person

rule "refine marketing consent"
    whenever
        (NOT userWithdrawsConsent(r, s)) SINCE userGivesConsent(r, s)
    refine
        marketingConsent(r, s)

assume true objectToSimilarEmailMarketing
assume true isNaturalPerson

assume false fax
assume false automatedCall

rule "stronger_consent"
    whenever
        automatedCommunication(s, r, "marketing", c)
    oblige
        marketingConsent(r, s)
        over18(r)
    enforceable suppressing automatedCommunication

replace
    strengthen
        article "13" paragraph "1"
    by
        rule "stronger_consent"