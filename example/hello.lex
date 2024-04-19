law "GDPR" "REGULATION (EU) 2016/679 OF THE EUROPEAN PARLIAMENT AND OF THE COUNCIL of 27 April 2016 on the protection of natural persons with regard to the processing of personal data and on the free movement of such data, and repealing Directive 95/46/EC (General Data Protection Regulation)"

import comments

type processingid is int
type processorid is int
type consentid is int
type dataid is int
type userid is int
type id is int # only a placeholder such that every argument has a type
type purpose is string

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

observable event Nominates
"""controller {y} nominates processor {x} to process personal data on {y}'s behalf"""
    # TODO: update types according to intended meaning
    #       of the arguments
    y: processorid
    x: processorid

observable event PersonalData
"""
{z} is personal data for data subject {w}
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

observable event HasPurpose
"""
processing operation {ep} has purpose {prp}
"""
    ep: processingid
    prp: purpose

observable event GiveConsent
"""
data subject {w} gives consent {c}
"""
    w: userid
    c: consentid

observable event Authorizes
"""
consent {c} authorizes usage of personal data for purpose {prp}
"""
    c: consentid
    prp: purpose


observable event isMinor
    w: id

chapter "2" "Principles"
article "5" "Principles relating to processing of personal data"
paragraph "1"
point "a" # labels must currently contain redundant information
    rule
"""
Art. 5(1) Personal data shall be: [...]
(a) processed lawfully, fairly and in a transparent manner in relation to the
 data subject (‘lawfulness, fairness and transparency’);
"""
    whenever
        PersonalDataProcessing(ep, x, z)
    oblige
        lawfulness(ep)
        fairness(ep)
        transparency(ep)
enforceable suppressing PersonalDataProcessing 

article "6" "Lawfulness of processing"
paragraph "1"
point "a"
rule
"""
Art. 6(1) Processing shall be lawful only if and to the extent that at least one of the following applies:
(a) the data subject has given consent to the processing of his or her personal data for one or more specific purposes;
"""
    whenever 
        PersonalDataProcessing(ep, x, z)
        HasPurpose(ep, prp)
        (ONCE GiveConsent(ehc, c) AND Authorizes(c, prp))
        (ONCE Nominates(y, x))
        PersonalData(z, w)
    constitute
        lawfulness(ep)
enforceable causing lawfulness
       
article "8" "Conditions applicable to child's consent in relation to information society services"
article[1] "II" "dummy level to try out sublevels"
article[2] "A" "dummy level to try out sublevels"
# article[6] "iv" "dummy level to try out sublevels"
# article[1] "B" "dummy level to try out sublevels"
paragraph "1"
rule 
    whenever isMinor(w) # {w} is the same type as {w} in "6(1)(a)"
    except "GDPR 6(1)(a)"
    # except "Art. 6(1)(a) GDPR"
