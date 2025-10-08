refine paper

type session_id is string
type data_type  is string
type fun_name   is string

observable event ReceiveConsentOwner
    u : session_id
    
observable event ReceiveConsent
    s : string

suppressable event ReadData
    f : fun_name
    t : data_type
    u : session_id

suppressable event WriteData
    f : fun_name
    t : data_type
    u : session_id
	
refine type data_subject is session_id
refine type entity       is string
refine type data         is data_type
refine type activity     is fun_name

rule "refine_data_processing"
    whenever
        ReadData(f, t, u) OR WriteData(f, t, u)
    refine
        DataProcessing("MyCompany", "MyCompany", f, t)

rule "refine_personal_data"
    whenever
        ReadData(f, t, u) OR WriteData(f, t, u)
        t = "ip" OR t = "user_agent"
    refine
        PersonalData(t, u)

assume true IsFair
assume true IsTransparent

rule "refine_iscollect"
    whenever
        ReadData(f, t, u) OR WriteData(f, t, u)
        f = "ingress"
    refine
        IsCollection(f)

rule "refine_giveconsent"
    whenever
        ReceiveConsentOwner(u)
        ReceiveConsent("statistics")
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
        ONCE (EXISTS b. DataProcessing(pr, c, b, d) AND PersonalData(d, ds) AND IsCollection(b))
    assume fulfilled
        
rule "consent_before_collection"
    whenever
        DataProcessing(pr, c, a, d)
        IsCollection(a)
        PersonalData(d, ds)
    oblige
        EXISTS p. ONCE GiveConsent(ds, p, c)
    enforceable suppressing DataProcessing

replace
    strengthen
        article "6" paragraph "1" point "a"
    by
        rule "new_lawfulness"
        rule "collection_before_processing"
        rule "consent_before_collection"
