import prOnto.*
import dapreco.*
import rioOnto.*

article "5"
paragraph "5(1)"
point "5(1)(a)"
rule
    whenever
        PersonalDataProcessing(ep, x, z)
        nominates(edp, y, x) 
        PersonalData(z, w)
    oblige
        lawfulness(ep)
        fairness(ep)
        transparency(ep)
enforceable suppressing PersonalDataProcessing 
                
article "6"
paragraph "6(1)"
point "6(1)(a)"
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
       
article "8"
paragraph "8(1)"
rule 
    whenever isMinor(w)
    except "6(1)(a)"
