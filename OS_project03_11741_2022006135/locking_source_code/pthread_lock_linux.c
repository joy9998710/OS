#include <stdio.h>
#include <pthread.h>

int shared_resource = 0;

#define NUM_ITERS 10
#define NUM_THREADS 10
int n = NUM_THREADS;

void lock();
void unlock();
extern int test_and_set(int *lock);
int target = 0;

void lock()
{
    while(test_and_set(&target) != 0);
}

void unlock()
{
    target = 0;
}


void* thread_func(void* arg) {
    int tid = *(int*)arg;
    
    lock();
    
        for(int i = 0; i < NUM_ITERS; i++)    shared_resource++;
    
    unlock();
    
    pthread_exit(NULL);
}

int main() {
    pthread_t threads[n];
    int tids[n];
    
    for (int i = 0; i < n; i++) {
        tids[i] = i;
        pthread_create(&threads[i], NULL, thread_func, &tids[i]);
    }
    
    for (int i = 0; i < n; i++) {
        pthread_join(threads[i], NULL);
    }

    printf("shared: %d\n", shared_resource);
    
    return 0;
}