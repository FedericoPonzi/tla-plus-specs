The Three-Phase Commit Protocol (3PC) is a distributed transaction protocol used to ensure the consistency of 
distributed databases or systems where multiple participants need to agree on whether a transaction should be 
committed or aborted. It is an improvement over the Two-Phase Commit (2PC) protocol, aiming to eliminate some 
f the issues related to blocking and uncertainty that can occur in 2PC. The 3PC protocol divides the commit 
process into three phases: the "CanCommit" phase, the "PreCommit" phase, and the "DoCommit" phase.

3pc achieves liveness as it can commit in the event of failures as it can just timeout and retry, but it fails on 
correctness for async networks with a single network delayed TC or RM (network partition).

Running this spec with NetworkPartitions = TRUE leads to a stack trace in which one RM goes to Committed and the other 
one along with TM go to AbortedTransaction.


Resources:
* https://www.cs.columbia.edu/~du/ds/assets/lectures/lecture17.pdf
* http://muratbuffalo.blogspot.com/2018/12/2-phase-commit-and-beyond.html
* Diagram: https://en.wikipedia.org/wiki/File:Three-phase_commit_diagram.svg
