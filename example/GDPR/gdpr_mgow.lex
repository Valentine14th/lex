law "GDPR"

import formex GDPR

article "5" "Principles relating to processing of personal data"

type activity
type data
type data_subject
type purpose is string
type entity
type interest

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

observable predicate IsCollect
    """Data processing activity {a} is a data collection activity"""
    a : activity

suppressable predicate HasPurpose
    """Data processing activity {a} has purpose {p}"""
    a : activity
    p : purpose

internal predicate CompatibleWithPurpose
    """Data processing activity {a} is compatible with purpose {p}"""
    a : activity
    p : purpose

observable predicate IsSpecified
    """Purpose {p} is specified"""
    p : purpose

observable predicate IsExplicit
    """Purpose {p} is explicit"""
    p : purpose

observable predicate IsLegitimate
    """Purpose {p} is legitimate"""
    p : purpose

observable predicate ActivityArticle89_1
    """Activity {a} is one of the activities described in Article 89(1)"""
    a : activity

observable predicate IsAdequate
    """Data {d} is adequate in relation to purpose {p}"""
    d : data
    p : purpose

observable predicate IsRelevant
    """Data {d} is relevant in relation to purpose {p}"""
    d : data
    p : purpose

observable predicate IsLimitedToWhatIsNecessary
    """Data {d} is limited to what is necessary in relation to purpose {p}"""
    d : data
    p : purpose

observable predicate IsAccurate
    """Data {d} is accurate in relation to purpose {p}"""
    d : data
    p : purpose

observable predicate IsUpToDate
    """Data {d} is up to date in relation to purpose {p}, where necessary"""
    d : data
    p : purpose

causable observable event Delete
    """Data {d} is deleted"""
    d : data

causable observable event Rectify
    """Data {d} is rectified"""
    d : data

observable predicate EnsuresAppropriateSecurity
    """Activity {a} ensures appropriate security of data {d}, including ... (see Art. 5(1)(f))"""
    a : activity
    d : data

suppressable event Stored
    """Data {d} is stored"""
    d : data

observable predicate AllowsIdentification
    """Data {d} allows the identification of its data subject {ds}"""
    d : data
    ds : data_subject

observable predicate IsNecessary
    """Data {d} is necessary to fulfill purpose {p}"""
    d : data
    p : purpose

observable predicate TechnicalAndOrganisationalMeasures
    """Appropriate technical and organisational measures have been taken to justify an exception to storage limiation requirements for activity {a} as by Article 89(1)"""
    a : activity

observable predicate JustifiesStorage
    """Activity {a} justifies the storage of data {d}"""
    a : activity
    d : data

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
    transparently enforceable suppressing DataProcessing

point "b"

rule "must_have_purpose"
    whenever
        DataProcessing(pr, c, a, d)
        PersonalData(d, ds)
    oblige 
        EXISTS p. HasPurpose(a, p)
    transparently enforceable suppressing DataProcessing

rule "purpose_conditions"
    whenever
        HasPurpose(a, p)
    oblige
        IsSpecified(p)
        IsExplicit(p)
        IsLegitimate(p)
    transparently enforceable suppressing HasPurpose

rule "purpose_limitation"
    whenever
        DataProcessing(pr, co, a, d)
        PersonalData(d, ds)
    oblige
        EXISTS c, p. CompatibleWithPurpose(a, p) AND ONCE (DataProcessing(pr, co, c, d) AND IsCollect(c) AND HasPurpose(c, p))
    transparently enforceable suppressing DataProcessing

rule "archiving_purpose"
    whenever
        ActivityArticle89_1(a)
    constitute
        CompatibleWithPurpose(a, "Archiving")

point "c"

rule
    whenever
        DataProcessing(pr, co, a, d)
        PersonalData(d, ds)
        HasPurpose(a, p)
    oblige 
        IsAdequate(d, p)
        IsRelevant(d, p)
        IsLimitedToWhatIsNecessary(d, p)
    transparently enforceable suppressing DataProcessing

point "d"

rule "accurate_and_up_to_date"
    whenever
        DataProcessing(pr, co, a, d)
        HasPurpose(a, p)
    oblige
        IsAccurate(d, p)
        IsUpToDate(d, p)
    transparently enforceable suppressing DataProcessing

note "without delay"

rule "accuracy_deletion"
    whenever
        NOT IsAccurate(d, p)
        EXISTS c. ONCE (DataProcessing(pr, co, c, d) AND IsCollect(c) AND HasPurpose(c, p))
    oblige
        Delete(d) OR Rectify(d)
    transparently enforceable causing Delete Rectify

point "e"

rule "temporal_storage_limitation"
    whenever
        Stored(d)
        PersonalData(d, ds)
        AllowsIdentification(d, ds)
        EXISTS c. ONCE (DataProcessing(pr, co, c, d) AND IsCollect(c) AND HasPurpose(c, p))
    oblige 
        IsNecessary(d, p)
    transparently enforceable suppressing Stored

rule "storage_limitation_exception"
    whenever
        ActivityArticle89_1(a) AND TechnicalAndOrganisationalMeasures(a) AND JustifiesStorage(a, d)
    except
        rule "temporal_storage_limitation"

point "f"

rule
    whenever
        DataProcessing(p, c, a, d)
    oblige
        EnsuresAppropriateSecurity(a, d)
    transparently enforceable suppressing DataProcessing

article "6" "Lawfulness of processing"

observable event GiveConsent
    """Data subject {ds} gives consent to processor {c} to use data {d} for purpose {p}"""
    ds : data_subject
    d : data
    p : purpose
    c : entity

observable predicate IsNecessaryForLegitimateInterest
    """Data processing activity {a} is necessary to protect the interest {i} of party {e}"""
    a : activity
    e : entity
    i : interest


observable predicate IsPublicAuthority
    """Entity {e} is a public authority"""
    e : entity

observable predicate IsPerformanceOfPublicAuthorityTask
    """Data processing activity {a} is part of the performance of a public authority task"""
    a : activity
  
paragraph "1"

paragraph[1] "1"

point "a"

rule
    whenever
        DataProcessing(pr, c, a, d)
        PersonalData(d, ds)
        ONCE GiveConsent(ds, d, p, c)
    constitute
        IsLawful(a)

point "f"

rule
    whenever
        DataProcessing(p, c, a, d)
        IsNecessaryForLegitimateInterest(a, e, i)
    constitute
        IsLawful(a)

paragraph[1] "2"

rule
    whenever
        IsPublicAuthority(p)
        IsPerformanceOfPublicAuthorityTask(a)
    except
        paragraph[1] "1" point "f"
