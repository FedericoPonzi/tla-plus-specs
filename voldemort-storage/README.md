## Voldemort storage
This is my solution to Murat Demibras first tla+ project. I decided to not reuse the provided 
template.

From: https://muratbuffalo.blogspot.com/2016/11/modeling-replicated-storage-system-in.html?m=1
 
> I assigned the students to model Voldemort with client-side routing as their first project.

> Here is the protocol. The client reads the highest version number "hver" from the read quorum (ReadQ). 
The client then writes to the write quorum nodes (WriteQ) the store the updated record with "hver+1" 
version number. The storage nodes can crash or recover, provided that no more than FAILNUM number of 
nodes are crashed at any moment. Our WriteQ and ReadQ selection will consist of the lowest id storage 
nodes that are up (currently not failed).

> I asked the students to model check with different combinations of ReadQ, WriteQ, and FAILNUM, and 
figure out the relation that needs to be satisfied among these configuration parameters in order to 
ensure that the protocol satisfies the single-copy consistency property. I wanted my students to see 
how consistency can be violated as a result of a series of unfortunate events (such as untimely node 
death and recoveries). The model checker is very good for producing counterexamples where consistency 
is violated.
> We simplified things by modeling the storing (and updating) of just a single data item, so we didn't have to model the hashing part. We also used shared memory. The client directly writes (say via an RPC) to the db of the storage nodes. 
> I also gave the students the template for the model. 

I've committed the base template separately in this repo (check history) in case you want to give it a stab yourself.

