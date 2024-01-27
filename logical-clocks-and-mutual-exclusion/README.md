# Lamport clocks
Lamport clocks used to solve the mutual exclusion problem, as seen in Lamport's paper: [Time, Clocks, and the Ordering of Events in a Distributed System](https://lamport.azurewebsites.net/pubs/time-clocks.pdf).

Mutual exclusion rules:
(I) A process which has been granted the resource must release it before it
can be granted to another process. 
(II) Different requests for the resource must be granted in the order in which
they are made. 
(III) If every process which is granted the resource eventually releases it, then every request is eventually granted.

safety: 
    * Only a single process can access the resource at a time. Checked via assert.
liveness:
    * All processes that requested access to the resource, eventually get it.
