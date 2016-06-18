# CoqLACL
This repository contains Coq files implementing type theoretical semantics for a number of natural language phenomena in Coq. The files have been compiled using Coq 8.5. The files are as follows:

MainCoq.v: This is the main file that includes a number of ideas developed using Luo's TTCS for natural language semantics. It includes the CNs as types idea, subtyping, Pustejovsky's book example formalized as a record type, dot.types, quantifiers, comparatatives and a simple model of tense among other things

adjectives.v: Some ideas on multidimensional adjectives and the sigma type treatment (via dependent records) of intersective adjectives

CN_predhyp.v: Contains ideas proposals solutions along with proofs associated with issues that arise if one takes the common nouns as types view. Predicational, hypothetical and negated sentences are taking care of. 

FraCasCoq.v: This includes a number of proofs for a number of examples from the FraCas.

test.v: This is a file quite close to MainCoq.v with the addition of some automated tactics to be used with FraCasCoq.v

Individuation.v: This contains a library for the individuation criteria associated with common nouns. It contains proofs for some problematic aspects of individuation with dot types (e.g. John picked up and mastered three books-> John picked up three physical objects and mastered three informational objects)

Records.v: Some simple examples of Type Theory with Records

DAVIDSON.v: A small, typed, neo-Davidsonian toy grammar

MontagovianLexiconToy.v: a toy grammar based on the Retore's Montagovian Generative Lexicon including coercions, dot types and polymorphic coordination. 
