# Lamport clocks
Lamport clocks used to solve the mutual exclusion problem, as seen in Lamport's paper: [Time, Clocks, and the Ordering of Events in a Distributed System](https://lamport.azurewebsites.net/pubs/time-clocks.pdf).

Mutual exclusion rules:
1. A process which has been granted the resource must release it before it can be granted to another process. 
2. Different requests for the resource must be granted in the order in which they are made. 
3. If every process which is granted the resource eventually releases it, then every request is eventually granted.

Safety: 
    * Only a single process can access the resource at a time. Checked via assert.

Liveness:
    * All processes that requested access to the resource, eventually get it.

As we're just trying to show a way to use lamport clocks to solve a synchronization problem, the algorithm presented in the paper above and modeled here doesn't deal with crashes.

When the `ProcessCanFail` constant in the config to TRUE, the smallest process ("0") will never send an AckRequestResource back (akin to a crash).
This breaks the liveness property.
