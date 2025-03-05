law "GDPR"

import formex GDPR

article "5" "Principles relating to processing of personal data"

type activity
type data
type data_subject
type purpose is string
type entity

observable predicate PersonalData
    """Data {d} is personal data of data subject {ds}"""
    d : data
    ds : data_subject

suppressable event DataProcessing
    """Data {d} is processed by processor {p} on behalf of controller {c} as part of data processing activity {a}"""
    p : entity
    c : entity
    a : activity
    d : data

internal predicate IsLawful 
    """Data processing activity {a} is lawful"""
    a : activity

observable predicate IsFair
    """Data processing activity {a} is fair"""
    a : activity

observable predicate IsTransparent
    """Data processing activity {a} is transparent in relation to data subject {ds}"""
    a : activity
    ds : data_subject

observable predicate IsCollection
    """Data processing activity {a} is a data collection activity"""
    a : activity

paragraph "1"
point "a"

rule 
    whenever
        DataProcessing(p, c, a, d)
        PersonalData(d, ds)
    oblige
        IsLawful(a)
        IsFair(a)
        IsTransparent(a, ds)
    enforceable suppressing DataProcessing

article "6" "Lawfulness of processing"

type interest

observable event GiveConsent
    """Data subject {ds} gives consent to processor {c} to use their data for purpose {p}"""
    ds : data_subject
    p : purpose
    c : entity

observable predicate IsNecessaryForLegitimateInterest
    """Data processing activity {a} is necessary to protect the interest {i} of party {e}"""
    a : activity
    e : entity
    i : interest

observable predicate IsOverridenByDataSubjectInterests
    """Interest {i} of entity {e} is overriden by the interests of data subject {ds}, in particular when {ds} is a child"""
    e : entity
    i : interest
    ds : data_subject

paragraph "1"
point "a"

rule
    whenever
        DataProcessing(pr, c, a, d)
        PersonalData(d, ds)
        ONCE GiveConsent(ds, p, c)
    constitute
        IsLawful(a)

point "f"

rule "legitimate_interest"
    whenever
        DataProcessing(p, c, a, d)
        IsNecessaryForLegitimateInterest(a, e, i)
    constitute
        IsLawful(a)

rule
    whenever
        PersonalData(d, ds)
        IsOverridenByDataSubjectInterests(e, i, ds)
    except
        rule "legitimate_interest"
