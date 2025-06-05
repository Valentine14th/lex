law "EPD" "Directive 2002/58/EC of the European Parliament and of the Council of 12 July 2002 concerning the processing of personal data and the protection of privacy in the electronic communications sector (Directive on privacy and electronic communications)"

# import formex e_privacy_directive

type person
type purpose is string
type productCategory is string

internal event automatedCommunication
    """ person {receiver} receives an
    automated message about a product or
    service from category {c} from person
    {sender} for purpose {p}"""
    sender: person
    receiver: person
    p: purpose
    c: productCategory

causable suppressable event automatedCall
    """ person {r} receives an
    automated call about a product or
    service from category {c} from
    person {s} for purpose {p}"""
    r: person 
    s: person
    p: purpose
    c: productCategory

causable suppressable event fax
    """ person {r} receives a
    fax about a product or
    service from category {c} from
    person {s} for purpose {p}"""
    r: person 
    s: person
    p: purpose
    c: productCategory

causable suppressable event email
    """ person {r} receives an
    email about a product or
    service from category {c} from
    person {s} for purpose {p}"""
    r: person 
    s: person
    p: purpose
    c: productCategory

observable event obtainedEmailForCategory
    """ person {r} has obtained the email
    address of person {s} for a product or
    service from category {c}"""
    r: person
    s: person
    c: productCategory

observable event marketingConsent
    """ person {s} has consented to receive
    automated marketing communication from
    person {r} """
    r: person
    s: person

observable event objectToSimilarEmailMarketing
    """ person {r} has objected to receiving
    similar email marketing communication from
    person {s} for products or services from
    category {c}"""
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

article "1" "Scope and aim"
paragraph "1"
note "This Directive harmonises the provisions of the Member States required to ensure an equivalent level of protection of fundamental rights and freedoms, and in particular the right to privacy, with respect to the processing of personal data in the electronic communication sector and to ensure the free move- ment of such data and of electronic communication equipment and services in the Community."

paragraph "2"
note "The provisions of this Directive particularise and comple- ment Directive 95/46/EC for the purposes mentioned in para- graph 1. Moreover, they provide for protection of the legitimate interests of subscribers who are legal persons."

paragraph "3"
note "This Directive shall not apply to activities which fall outside the scope of the Treaty establishing the European Community, such as those covered by Titles V and VI of the Treaty on European Union, and in any case to activities concerning public security, defence, State security (including the economic well-being of the State when the activities relate to State security matters) and the activities of the State in areas of criminal law"

article "2" "Definitions"
point "(a)" "user"
point "(b)" "traffic data"
point "(c)" "location data"
point "(d)" "communication"
point "(e)" "call"
point "(f)" "consent"
point "(g)" "value added service"
point "(h)" "electronic mail"

article "3" "Services covered"
paragraph "1"
paragraph "2"
paragraph "3"

article "4" "Security"
paragraph "1"
paragraph "2"

article "5" "Confidentiality of communications"
paragraph "1"
paragraph "2"
paragraph "3"

article "6" "Traffic data"
paragraph "1"
paragraph "2"
paragraph "3"
paragraph "4"
paragraph "5"
paragraph "6"

article "7" "Itemised billing"
paragraph "1"
paragraph "2"

article "8" "Presentation and restriction of calling and connected line identification"
paragraph "1"
paragraph "2"
paragraph "3"
paragraph "4"
paragraph "5"
paragraph "6"

article "9" "Location data other than traffic data"
paragraph "1"
paragraph "2"
paragraph "3"

article "10" "Exceptions"
point "(a)"
point "(b)"

article "11" "Automatic call forwarding"

article "12" "Directories of subscribers"
paragraph "1"
paragraph "2"
paragraph "3"
paragraph "4"

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

article "14" "Technical features and standardisation"
paragraph "1"
paragraph "2"
paragraph "3"

article "15" "Application of certain provisions of Directive 95/46/EC"
paragraph "1"
paragraph "2"
paragraph "3"

article "16" "Transitional arrangements"
paragraph "1"
paragraph "2"

article "17" "Transposition"
paragraph "1"
paragraph "2"

article "18" "Review"

article "19" "Repeal"

article "20" "Entry into force"

article "21" "Addresses"
note "This Directive is addressed to the Member States."
