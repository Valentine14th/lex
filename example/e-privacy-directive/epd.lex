law "EPD" "Directive 2002/58/EC of the European Parliament and of the Council of 12 July 2002 concerning the processing of personal data and the protection of privacy in the electronic communications sector (Directive on privacy and electronic communications)"

type person
type purpose is string
type productCategory is string

internal event automatedCommunication
    """ person {receiver} receives an automated message about a product or service from category {c} from person {sender} for purpose {p}"""
    sender: person
    receiver: person
    p: purpose
    c: productCategory

causable suppressable event automatedCall
    """ person {r} receives an automated call about a product or service from category {c} from person {s} for purpose {p}"""
    r: person 
    s: person
    p: purpose
    c: productCategory

causable suppressable event fax
    """ person {r} receives a fax about a product or service from category {c} from person {s} for purpose {p}"""
    r: person 
    s: person
    p: purpose
    c: productCategory

causable suppressable event email
    """ person {r} receives an email about a product or service from category {c} from person {s} for purpose {p}"""
    r: person 
    s: person
    p: purpose
    c: productCategory

observable event obtainedEmailForCategory
    """ person {r} has obtained the email address of person {s} for a product or service from category {c}"""
    r: person
    s: person
    c: productCategory

observable event marketingConsent
    """ person {s} has consented to receive automated marketing communication from person {r} """
    r: person
    s: person

observable event objectToSimilarEmailMarketing
    """ person {r} has objected to receiving similar email marketing communication from person {s} for products or services from category {c}"""
    r: person
    s: person
    c: productCategory

observable event isNaturalPerson
    """ person {s} is a natural person """
    s: person

rule "automated call communication"
    whenever
        automatedCall(s, r, p, c)
    constitute
        automatedCommunication(s, r, p, c)

rule "fax communication"
    whenever
        fax(s, r, p, c)
    constitute
        automatedCommunication(s, r, p, c)

rule "email communication"
    whenever
        email(s, r, p, c)
    constitute
        automatedCommunication(s, r, p, c)


article "13" "Unsolicited communications"
paragraph "1"

rule "marketing consent requirement"
    whenever
        automatedCommunication(s, r, "marketing", c)
    oblige
        marketingConsent(r, s)
    enforceable suppressing automatedCommunication

paragraph "2"

rule "marketing of similar products or services"
    whenever
        obtainedEmailForCategory(r, s, c)
        NOT objectToSimilarEmailMarketing(r, s, c)
    except
        article "13" paragraph "1"

paragraph "3"
paragraph "4"
paragraph "5"

rule 
    whenever
        isNaturalPerson(r)
    scope
        article "13" paragraph "1"
        article "13" paragraph "3"
