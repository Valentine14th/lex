law "GDPR"

import formex GDPR

type processingid is int
type processorid is int
type consentid is int
type dataid is int
type userid is int
type purpose is string

suppressable event PersonalDataProcessing
    """ {x} is processing personal data {z} as part of processing operation {ep} """
    ep: processingid
    x: processorid
    z: dataid

observable event Nominates
    """controller {y} nominates processor {x} to process personal data on {y}'s behalf"""
    y: processorid
    x: processorid

observable event PersonalData
    """ {z} is personal data for data subject {w} """
    z: dataid
    w: userid

internal event lawfulness
    """ processing {ep} is lawful """
    ep: processingid

internal event fairness
    """ processing {ep} is fair """
    ep: processingid

internal event transparency
    """ processing {ep} is transparent """
    ep: processingid

observable event HasPurpose
    """ processing operation {ep} has purpose {prp} """
    ep: processingid
    prp: purpose

observable event GiveConsent
    """ data subject {w} gives consent {c} """
    w: userid
    c: consentid

observable event Authorizes
    """ consent {c} authorizes usage of personal data for purpose {prp} """
    c: consentid
    prp: purpose


observable event isMinor
    """ data subject {w} is a minor """
    w: userid

chapter "II"
article "5"
paragraph "1"
point "a"
rule
    whenever
        PersonalDataProcessing(ep, x, z)
    oblige
        lawfulness(ep)
        fairness(ep)
        transparency(ep)
    enforceable suppressing PersonalDataProcessing

article "6"
paragraph "1"
point "1"
subpoint "a"
rule
    whenever 
        PersonalDataProcessing(ep, x, z)
        HasPurpose(ep, prp)
        (ONCE GiveConsent(w, c) AND Authorizes(c, prp))
        (ONCE Nominates(y, x))
        PersonalData(z, w)
    constitute
        lawfulness(ep)

article "8"
paragraph "1"
rule 
    whenever
        isMinor(w)
    except
        article "6" paragraph "1" point "1" subpoint "a"
