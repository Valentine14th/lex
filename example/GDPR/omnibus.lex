law "GDPR"

article "9"

paragraph "2"

point "k"

observable event DevelopmentOrOperationOfAISystem
    """Data processing activity {a} is conducted in the context of the development
       or operation of an AI system as defined in Article 3(1) of Regulation 2024/1689
      or an AI model."""
    a : activity

rule
    whenever
        DevelopmentOrOperationOfAISystem(a)
    except
        paragraph "1"
