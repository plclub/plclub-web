---
title: "Resource-Aware Session Types for Digital Contracts"
speaker: "Ankush Das"
semester: "SP21"
---

Abstract:

While there exist several successful techniques for supporting programmers in deriving static resource bounds for sequential code, analyzing the resource usage of message-passing concurrent processes poses additional challenges. To meet these challenges, this talk presents an analysis for statically deriving worst-case bounds on the computational complexity of message-passing processes, respectively. The analysis is based on novel resource-aware session types that describe resource contracts by allowing both messages and processes to carry potential and amortize cost. The talk then applies session types to implement digital contracts. Digital contracts are protocols that describe and enforce execution of a contract, often among mutually distrusting parties. Programming digital contracts comes with its unique challenges, which include describing and enforcing protocols of interaction, analyzing resource usage and tracking linear assets. The talk presents the type-theoretic foundations of Nomos, a programming language for digital contracts whose type system addresses the aforementioned domain-specific requirements. To express and enforce protocols, Nomos is based on shared binary session types rooted in linear logic. To control resource usage, Nomos uses resource-aware session types and automatic amortized resource analysis, a type-based technique for inferring resource bounds. To track assets, Nomos employs a linear type system that prevents assets from being duplicated or discarded. The talk concludes with future work directions on designing an efficient implementation for Nomos and making it robust to attacks from malicious entities.


30 min Homework:
Please visit the website (https://www.nomos-lang.org/), the main website for the Nomos language.
It contains a web interface that you can play around with.
You can either load an existing transaction, or create your own (if you are already familiar with Nomos).
If you load an existing transaction, you can type check it using the "Check / Elaborate" button.
If successful, you can submit the transaction using the "Submit" button.
Every transaction has a sender (issuer) associated with it, and before you submit a transaction,
you need to create a gas account for the sender (there is a button "Create Gas Account" with a name
and balance that can be used for it).

Once you submit a transaction, you can view the "Blockchain State". This shows you the channel
name where the contract is hosted, the session type of that channel, the state of the process,
and work done by and gas stored in the contract. You can see these updating as you submit more
transactions. You can also view the "Transaction History" which shows the sender's name, gas bound
and code of the transaction. You can also add print statements in the code which can be viewed
under "Execution Trace Messages".

There are 3 contracts (with increasing level of difficulty). The first is the storage contract (the hello
world of smart contracts). It stores a number inside a contract, with functionality to "set" and "get"
the value. The first transaction creates the contract (with integer value 0), the second one gets its
value, the third one sets its value to 100, and the final transaction gets its value again. You can
view some of this information in the "Execution Trace Messages".

The other two contracts are for wallets and an auction. I am not going to give more information
here, but try to figure out what they do!

If you are interested further, I would recommend reading the Nomos paper (Section 2) which
overviews the language.

https://www.cs.cmu.edu/~ankushd/docs/contract20.pdf

Have fun!
