# Dlog-zkp
Formalisation of Schnorr Protocol and other proofs (https://www.win.tue.nl/~berry/2WC13/LectureNotes.pdf)

Here is my plan to proceed:

1. I am going to write a concrete implementation of Group and Field 
    and their respective functions (addition, multiplication, division,
    etc), assuming the Schnorr group.
2. Then I write a power function that interacts between Group and 
    Field and show that it respects the vector-space axioms. 
3. Now that we have all the concrete implementation, we can 
   demonstrate that they are efficient.
4. Formalise others, e.g., AND, OR sigma protocol
5. Formalise some vote counting method where we can use our 
   sigma protocol library to demonstrate usability. 