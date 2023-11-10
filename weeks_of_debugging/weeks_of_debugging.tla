This code is from the talk SREcon20 Americas - Weeks of Debugging Can Save You Hours of TLA+ by Markus A. Kuppe.
https://www.youtube.com/watch?v=wjsI0lTSjIo


void *producer(void * arg) {
    while(1) {
        pthread_mutex_lock(&mutex); // acquire the lock
        while(count == buff_size) // check if the buffer is full
            pthread_cond_wait(&modify, &mutex);
        append(rand() % (10)); // produce!
            
        pthread_cond_signal(&modify); // broadcast that the buffer is full
        pthread_mutex_unlock(&mutex); // release the lock
    }
}

void *consumer(void * arg) {
    long report = 0;
    while(1) {
        pthread_mutex_lock(&mutex); // acquire the lock

        while(count == 0) // check if the buffer is empty
            pthread_cond_wait(&modify, &mutex); // wait for the buffer

        head(); // consume (we don't care about the value)
        pthread_cond_signal(&modify); // signal that the buffer is empty
        pthread_mutex_unlock(&mutex); // release the lock
            
        if (report++ % 10000 == 0) {
            printf("\n%ld values consumed", report);
        }
    }
}

It contains some concurrency bug, the goal of this spec is to spot it.

---- MODULE weeks_of_debugging ----
EXTENDS TLC

(* --algorithm weeks_of_debugging {
    variables mutex = {}, modify = {};

    fair process (Reader = 0) {

    }
    fair process (Writer = 0) {
        
    }

} *)


====

