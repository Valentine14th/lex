refine paper

type session_id is string
type data_class is string
type data_field is string
type data_id    is string

suppressable event read
    cls     : data_class
    field   : data_field
    id      : data_id
    caller  : session_id
    owner   : session_id
    purpose : purpose

suppressable event write
    cls     : data_class
    field   : data_field
    id      : data_id
    caller  : session_id
    value   : string
    owner   : session_id
    purpose : purpose

observable event input
    func    : string
    param   : string
    value   : string
    caller  : string
    purpose : string

refine type data_subject is session_id
refine type entity       is string
refine type data         is data_id
refine type activity     is purpose

rule "refine_data_processing"
    whenever
        read(cls, field, id, caller, owner, purpose) OR (EXISTS value. write(cls, field, id, caller, value, owner, purpose))
    refine
        DataProcessing("MyCompany", "MyCompany", purpose, id)

rule "refine_personal_data"
    whenever
        read(cls, field, id, caller, owner, purpose) OR (EXISTS value. write(cls, field, id, caller, value, owner, purpose))
        field = "ip" OR field = "user_agent"
    refine
        PersonalData(id, owner)

assume true IsFair
assume true IsTransparent

rule "refine_iscollect"
    whenever
        read(cls, field, id, caller, owner, purpose) OR (EXISTS value. write(cls, field, id, caller, value, owner, purpose))
        purpose = "ingress"
    refine
        IsCollection(purpose)

rule "refine_giveconsent"
    whenever
        input("ConsentView", "statistics", "true", caller, "service")
        input("ConsentView", "session", owner, caller, "service")
    refine
        GiveConsent(owner, "analytics", "MyCompany")

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
