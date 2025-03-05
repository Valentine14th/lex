### Refinement syntax sketchpad - not intended to compile or make sense

observable event phoneConsent
    u: user_id
    p: purpose

observable event emailConsent
    u: user_id
    p: purpose

internal event Consent
    u: user_id
    p: purpose

rule 1
    whenever
        phoneConsent(u, p)
    constitute
        Consent(u, p)

rule 2
    whenever
        emailConsent(u, p)
    constitute
        Consent(u, p)

rule 3
    whenever
        phoneConsent(u,p) OR emailConsent(u, p)
    constitute
        Consent(u, p)

rule 4
    whenever
        Consent(u, p)
    refine
        GiveConsent(u, "myfirm", p)

rule 5
    whenever
        phoneConsent(u, p)
    refine
        GiveConsent(u, "myfirm", p)

rule 6
    whenever
        emailConsent(u, p)
    refine
        GiveConsent(u, "myfirm", p)

rule 7
    whenever
        phoneConsent(u,p) OR emailConsent(u, p)
    refine
        GiveConsent(u, "myfirm", p)

rule
    whenever
        Processing ( processing , controller , processor , purpose , data )
        PersonalData ( data , data_subject )
    oblige
        Lawful ( processing , data_subject )
        Fair ( processing , data_subject )
        Transparent ( processing , data_subject )
    enforceable suppressing Processing
