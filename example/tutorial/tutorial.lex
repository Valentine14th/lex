law "GDPR"

type activity
type data
type data_subject
type purpose
type entity

predicate PersonalData
    """Data {d} is personal data of data subject {ds}"""
    d : data
    ds : data_subject

internal predicate IsLawful
    """Activity {a} is lawful"""
    a : activity

predicate IsFair
    """Activity {a} is fair"""
    a : activity

predicate IsTransparent
    """Activity {a} is transparent"""
    a : activity

event Process
    """Entity {p} processes data {d} as part of activity {a}"""
    p : entity
    a : activity
    d : data

event GiveConsent
    """Data subject {ds} consents that their data is used by {c} for purpose {p}"""
    ds : data_subject
    p : purpose
    c : entity

predicate IsMinor
    """Data subject {ds} is < 16"""
    ds : data_subject

article "5"
paragraph "1"
point "a"

rule
    whenever
        Process(p, a, d)
        PersonalData(d, ds)
    oblige
        IsLawful(a)
        IsFair(a)
        IsTransparent(a)

article "6"
paragraph "1"
point "a"

rule
    whenever
        Process(c, a, d)
        PersonalData(d, ds)
        ONCE GiveConsent(ds, p, c)
    constitute
        IsLawful(a)

article "8"
paragraph "1"

rule
    whenever
        Process(c, a, d)
        PersonalData(d, ds)
        IsMinor(ds)
    except
        article "6" paragraph "1" point "a"
  
