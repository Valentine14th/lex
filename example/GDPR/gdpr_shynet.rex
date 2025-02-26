refine gdpr_mgow

type session_id is int
type data_type  is string
type data_id    is int
type fun_name   is string

observable event ReceiveConsentSignal
    u : session_id

suppressable event ReadData
    f : fun_name
    d : data_id

suppressable event WriteData
    f : fun_name
    d : data_id

observable event Collect
    f : fun_name

observable predicate DataItem
    d : data_id
    t : data_type
    u : session_id

refine type data_subject is session_id
refine type entity       is string
refine type data         is data_id
refine type activity     is fun_name

rule "refine_data_processing"
    whenever
        ReadData(f, d) OR WriteData(f, d)
    refine
        DataProcessing("MyCompany", "MyCompany", f, d)

rule "refine_personal_data"
    whenever
        DataItem(d, t, u)
        t = "ip_address" OR t = "user_agent"
    refine
        PersonalData(d, u)

assume true IsFair
assume true IsTransparent

rule "refine_iscollect"
    whenever
        Collect(f)
    refine
        IsCollect(f)

rule "refine_giveconsent"
    whenever
        ReceiveConsentSignal(u)
    refine
        GiveConsent(u, "analytics", "MyCompany")

assume false IsNecessaryForLegitimateInterest
assume false IsOverridenByDataSubjectInterests

rule "new_lawfulness"
    whenever
        DataProcessing(pr, c, a, d)
        PersonalData(d, ds)
    constitute
        IsLawful(a)

rule "collection_before_processing"
    whenever
        DataProcessing(pr, c, a, d)
        PersonalData(d, ds)
    oblige
        ONCE (EXISTS b. DataProcessing(pr, c, b, d) AND PersonalData(d, ds) AND IsCollect(b))
    assume fulfilled
        
rule "consent_before_collection"
    whenever
        DataProcessing(pr, c, a, d)
        IsCollect(a)
        PersonalData(d, ds)
    oblige
        EXISTS p. ONCE GiveConsent(ds, p, c)
    enforceable suppressing DataProcessing

replace
    strengthen
        article "5" paragraph "1" point "a"
    by
        rule "new_lawfulness"
        rule "collection_before_processing"
        rule "consent_before_collection"