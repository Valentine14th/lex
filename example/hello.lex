import prOnto.*
import dapreco.*
import rioOnto.*

type processingid is int
type processorid is int
type dataid is int
type userid is int
type id is int # only a placeholder such that every argument has a type

# observable event
# causable event
# internal event
suppressable event PersonalDataProcessing
"""
{x} is processing personal data {z} as part
of processing operation {ep}
"""
    ep: processingid
    x: processorid
    z: dataid

observable event nominates
 """
 """
    # TODO: update types according to intended meaning
    #       of the arguments
    edp: processorid
    y: processorid
    x: processorid

observable event PersonalData
"""
"""
    # TODO: update types according to intended meaning
    #       of the arguments
    z: dataid
    w: id # TODO: what is {w} meant to be?

internal event lawfulness
"""
processing {ep} is lawful
"""
    ep: processingid

internal event fairness
"""
processing {ep} is fair
"""
    ep: processingid

internal event transparency
"""
processing {ep} is transparent
"""
    ep: processingid

observable event isBasedOn
"""
processing {ep} is based on {epu}
"""
    ep: processingid
    epu: id

observable event GiveConsent
"""
"""
    ehc: id
    w: id
    c: id

observable event AuthorizedBy
    eau: id
    epu: id
    c: id

observable event Purpose
    epu: id

observable event isMinor
    w: id

law "GDPR"
chapter "GDPR 2"
article "GDPR 2 5"
paragraph "GDPR 2 5(1)"
point "GDPR 2 5(1)(a)" # labels must currently contain redundant information
    rule whenever
        PersonalDataProcessing(ep, x, z)
        nominates(edp, y, x) 
        PersonalData(z, w)
    oblige
        lawfulness(ep)
        fairness(ep)
        transparency(ep)
enforceable suppressing PersonalDataProcessing 

article "GDPR 2 6"
paragraph "GDPR 2 6(1)"
point "GDPR 2 6(1)(a)"
rule
    whenever 
        PersonalDataProcessing(ep, x, z)
        isBasedOn(ep, epu)
        (ONCE GiveConsent(ehc, w, c))
        AuthorizedBy(eau, epu, c)
        nominates(edp, y, x)
        PersonalData(z, w)
        Purpose(epu)
    constitute 
        lawfulness(ep)
enforceable causing lawfulness
       
article "GDPR 2 8"
paragraph "GDPR 2 8(1)"
rule 
    whenever isMinor(w) # {w} is the same type as {w} in "6(1)(a)"
    except "GDPR 2 6(1)(a)"
