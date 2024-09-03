#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"

struct {
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

static struct proc *initproc;

int nextpid = 1;
extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
}

// Must be called with interrupts disabled
int
cpuid() {
  return mycpu()-cpus;
}

// Must be called with interrupts disabled to avoid the caller being
// rescheduled between reading lapicid and running through the loop.
struct cpu*
mycpu(void)
{
  int apicid, i;
  
  if(readeflags()&FL_IF)
    panic("mycpu called with interrupts enabled\n");
  
  apicid = lapicid();
  // APIC IDs are not guaranteed to be contiguous. Maybe we should have
  // a reverse map, or reserve a register to store &cpus[i].
  for (i = 0; i < ncpu; ++i) {
    if (cpus[i].apicid == apicid)
      return &cpus[i];
  }
  panic("unknown apicid\n");
}

// Disable interrupts so that we are not rescheduled
// while reading proc from the cpu structure
struct proc*
myproc(void) {
  struct cpu *c;
  struct proc *p;
  pushcli();
  c = mycpu();
  p = c->proc;
  popcli();
  return p;
}

//PAGEBREAK: 32
// Look in the process table for an UNUSED proc.
// If found, change state to EMBRYO and initialize
// state required to run in the kernel.
// Otherwise return 0.
static struct proc*
allocproc(int is_thread)
{
  struct proc *p;
  char *sp;

  acquire(&ptable.lock);

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == UNUSED)
      goto found;

  release(&ptable.lock);
  return 0;

found:
  p->state = EMBRYO;  
  if(!is_thread){
	  p->pid = nextpid++;
	  //Master thread
    p->tid = -1;
  }
  else{
	  //Copy process's pid
    struct proc *temp;
    int max_tid = -1;
    for(temp = ptable.proc; temp < &ptable.proc[NPROC]; temp++){
      if(temp->pid == myproc()->pid){
        if(temp->tid > max_tid){
          max_tid = temp->tid;
        }
      }
    }
    p->tid = max_tid + 1;
	  p->pid = myproc()->pid;
  }

  release(&ptable.lock);

  // Allocate kernel stack.
  //커널 스택으로 활용할 페이지 할당
  //커널 스택은 프로세스의 가상 메모리 공간의 커널 메모리 영역에 저장됨
  if((p->kstack = kalloc()) == 0){
    p->state = UNUSED;
    return 0;
  }
  //p->kstack은 이 페이지의 시작주소를 가리킴
  //stack이 아래로 확장되기에 이 주소가 현재 stack의 제일 마지막 주소

  //sp는kernel stack의 끝 주소 가리킴4KB만큼 추가 이동
  sp = p->kstack + KSTACKSIZE;

  // Leave room for trap frame.
  //trap frame을 저장하기 위한 공간
  sp -= sizeof *p->tf;
  //p->tf가 sp 주소 가리키게 해서 저기에 trap frame있다는 것을 저장
  p->tf = (struct trapframe*)sp;

  // Set up new context to start executing at forkret,
  // which returns to trapret.
  sp -= 4;
  //trap return address를 적어 마치 trap return으로 리턴하는 것처럼 보이게함
  *(uint*)sp = (uint)trapret;

  //process의 컨텍스트 저장하기 위해 스택 공간 확보
  sp -= sizeof *p->context;
  //context가 여기있음을 포인터로 적어줌
  p->context = (struct context*)sp;
  //일단 context 0으로 초기화
  memset(p->context, 0, sizeof *p->context);
  //forkret을 통해 종료하게 시킴
  p->context->eip = (uint)forkret;

  return p;
}

//PAGEBREAK: 32
// Set up first user process.
void
userinit(void)
{
  struct proc *p;
  extern char _binary_initcode_start[], _binary_initcode_size[];

  p = allocproc(0);
  
  initproc = p;
  if((p->pgdir = setupkvm()) == 0)
    panic("userinit: out of memory?");
  inituvm(p->pgdir, _binary_initcode_start, (int)_binary_initcode_size);
  p->sz = PGSIZE;
  memset(p->tf, 0, sizeof(*p->tf));
  p->tf->cs = (SEG_UCODE << 3) | DPL_USER;
  p->tf->ds = (SEG_UDATA << 3) | DPL_USER;
  p->tf->es = p->tf->ds;
  p->tf->ss = p->tf->ds;
  p->tf->eflags = FL_IF;
  p->tf->esp = PGSIZE;
  p->tf->eip = 0;  // beginning of initcode.S

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  // this assignment to p->state lets other cores
  // run this process. the acquire forces the above
  // writes to be visible, and the lock is also needed
  // because the assignment might not be atomic.
  acquire(&ptable.lock);

  p->state = RUNNABLE;

  release(&ptable.lock);
}

// Grow current process's memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  uint sz;
  struct proc *curproc = myproc();

  sz = curproc->sz;
  if(n > 0){
    if((sz = allocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  } else if(n < 0){
    if((sz = deallocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  }
  curproc->sz = sz;
  switchuvm(curproc);
  return 0;
}

// Create a new process copying p as the parent.
// Sets up stack to return as if from system call.
// Caller must set state of returned proc to RUNNABLE.
int
fork(void)
{
  int i, pid;
  struct proc *np;
  struct proc *curproc = myproc();

  // Allocate process.
  if((np = allocproc(0)) == 0){
    return -1;
  }

  // Copy process state from proc.
  // 부모 프로세스와 독립적인 페이지 테이블을 사용해야 하므로 페이지 테이블을 복사
  if((np->pgdir = copyuvm(curproc->pgdir, curproc->sz)) == 0){
    kfree(np->kstack);
    np->kstack = 0;
    np->state = UNUSED;
    return -1;
  }


  //부모 프로세스의 가상 메모리 공간 size 그대로 복사
  np->sz = curproc->sz;
  np->parent = curproc;
  //부모 프로세스의 trap frame 그대로 복사
  *np->tf = *curproc->tf;

  // Clear %eax so that fork returns 0 in the child.
  np->tf->eax = 0;

  //파일 시스템 모두 복사
  for(i = 0; i < NOFILE; i++)
    if(curproc->ofile[i])
      np->ofile[i] = filedup(curproc->ofile[i]);
  np->cwd = idup(curproc->cwd);

  //이름 복사
  safestrcpy(np->name, curproc->name, sizeof(curproc->name));

  pid = np->pid;

  acquire(&ptable.lock);

  np->state = RUNNABLE;

  release(&ptable.lock);

  return pid;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait() to find out it exited.
void
exit(void)
{
  struct proc *curproc = myproc();
  struct proc *p;
  int fd;

  if(curproc->tid >= 0){
    curproc = curproc->parent;
  }

  if(curproc == initproc)
    panic("init exiting");

  //master thread 종료 전 모든 스레드 종료
  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == curproc->pid && p->tid >= 0){
      freeproc2(p);
    }
  }
  release(&ptable.lock);


  // Close all open files.
  for(fd = 0; fd < NOFILE; fd++){
    if(curproc->ofile[fd]){
      fileclose(curproc->ofile[fd]);
      curproc->ofile[fd] = 0;
    }
  }
  

  begin_op();
  iput(curproc->cwd);
  end_op();
  curproc->cwd = 0;

  acquire(&ptable.lock);

  // Parent might be sleeping in wait().
  wakeup1(curproc->parent);

  // Pass abandoned children to init.
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->parent == curproc){
      p->parent = initproc;
      if(p->state == ZOMBIE)
        wakeup1(initproc);
    }
  }

  // Jump into the scheduler, never to return.
  curproc->state = ZOMBIE;
  sched();
  panic("zombie exit");
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(void)
{
  struct proc *p;
  int havekids, pid;
  struct proc *curproc = myproc();
  
  acquire(&ptable.lock);
  for(;;){
    // Scan through table looking for exited children.
    havekids = 0;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->parent != curproc)
        continue;
      havekids++;
      if(p->state == ZOMBIE){
        // Found one.
        pid = p->pid;
        kfree(p->kstack);
        p->kstack = 0;
        freevm(p->pgdir);
        p->pid = 0;
        p->parent = 0;
        p->name[0] = 0;
        p->killed = 0;
        p->tid = 0;
        p->state = UNUSED;
        release(&ptable.lock);
        return pid;
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || curproc->killed){
      release(&ptable.lock);
      return -1;
    }

    // Wait for children to exit.  (See wakeup1 call in proc_exit.)
    sleep(curproc, &ptable.lock);  //DOC: wait-sleep
  }
}

//PAGEBREAK: 42
// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run
//  - swtch to start running that process
//  - eventually that process transfers control
//      via swtch back to the scheduler.
void
scheduler(void)
{
  struct proc *p;
  struct cpu *c = mycpu();
  c->proc = 0;
  
  for(;;){
    // Enable interrupts on this processor.
    sti();

    // Loop over process table looking for process to run.
    acquire(&ptable.lock);
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->state != RUNNABLE){
        if(p->state == ZOMBIE){
          continue;
        }
        continue;
      }
      // Switch to chosen process.  It is the process's job
      // to release ptable.lock and then reacquire it
      // before jumping back to us.
      c->proc = p;
      switchuvm(p);
      p->state = RUNNING;

      swtch(&(c->scheduler), p->context);
      switchkvm();

      // Process is done running for now.
      // It should have changed its p->state before coming back.
      c->proc = 0;
    }
    release(&ptable.lock);

  }
}

// Enter scheduler.  Must hold only ptable.lock
// and have changed proc->state. Saves and restores
// intena because intena is a property of this
// kernel thread, not this CPU. It should
// be proc->intena and proc->ncli, but that would
// break in the few places where a lock is held but
// there's no process.
void
sched(void)
{
  int intena;
  struct proc *p = myproc();

  if(!holding(&ptable.lock))
    panic("sched ptable.lock");
  if(mycpu()->ncli != 1)
    panic("sched locks");
  if(p->state == RUNNING)
    panic("sched running");
  if(readeflags()&FL_IF)
    panic("sched interruptible");
  intena = mycpu()->intena;
  swtch(&p->context, mycpu()->scheduler);
  mycpu()->intena = intena;
}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  acquire(&ptable.lock);  //DOC: yieldlock
  myproc()->state = RUNNABLE;
  sched();
  release(&ptable.lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch here.  "Return" to user space.
void
forkret(void)
{
  static int first = 1;
  // Still holding ptable.lock from scheduler.
  release(&ptable.lock);

  if (first) {
    // Some initialization functions must be run in the context
    // of a regular process (e.g., they call sleep), and thus cannot
    // be run from main().
    first = 0;
    iinit(ROOTDEV);
    initlog(ROOTDEV);
  }

  // Return to "caller", actually trapret (see allocproc).
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  struct proc *p = myproc();
  
  if(p == 0)
    panic("sleep");

  if(lk == 0)
    panic("sleep without lk");

  // Must acquire ptable.lock in order to
  // change p->state and then call sched.
  // Once we hold ptable.lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup runs with ptable.lock locked),
  // so it's okay to release lk.
  if(lk != &ptable.lock){  //DOC: sleeplock0
    acquire(&ptable.lock);  //DOC: sleeplock1
    release(lk);
  }
  // Go to sleep.
  p->chan = chan;
  p->state = SLEEPING;

  sched();

  // Tidy up.
  p->chan = 0;

  // Reacquire original lock.
  if(lk != &ptable.lock){  //DOC: sleeplock2
    release(&ptable.lock);
    acquire(lk);
  }
}

//PAGEBREAK!
// Wake up all processes sleeping on chan.
// The ptable lock must be held.
static void
wakeup1(void *chan)
{
  struct proc *p;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == SLEEPING && p->chan == chan)
      p->state = RUNNABLE;
}

// Wake up all processes sleeping on chan.
void
wakeup(void *chan)
{
  acquire(&ptable.lock);
  wakeup1(chan);
  release(&ptable.lock);
}

// Kill the process with the given pid.
// Process won't exit until it returns
// to user space (see trap in trap.c).
int
kill(int pid)
{
  struct proc *p;
  int found = 0;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == pid && p->tid == -1){
      p->killed = 1;
      found = 1;
    }
    if(p->state == SLEEPING){
      p->state = RUNNABLE;
    }
    if(found){
      release(&ptable.lock);
      return 0;
    }
  }
  release(&ptable.lock);
  return -1;
}

//PAGEBREAK: 36
// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [EMBRYO]    "embryo",
  [SLEEPING]  "sleep ",
  [RUNNABLE]  "runble",
  [RUNNING]   "run   ",
  [ZOMBIE]    "zombie"
  };
  int i;
  struct proc *p;
  char *state;
  uint pc[10];

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    cprintf("%d %s %s", p->pid, state, p->name);
    if(p->state == SLEEPING){
      getcallerpcs((uint*)p->context->ebp+2, pc);
      for(i=0; i<10 && pc[i] != 0; i++)
        cprintf(" %p", pc[i]);
    }
    cprintf("\n");
  }
}

void
freeproc(struct proc *p){
  int fd;
  for(fd = 0; fd < NOFILE; fd++){
    if(p->ofile[fd]){
      fileclose(p->ofile[fd]);
        p->ofile[fd] = 0;
    }
  }
	if(p->kstack){
		kfree(p->kstack);
		p->kstack = 0;
	}
  if(p->pgdir){
      deallocuvm(p->pgdir, p->sz, p->base);
		  p->pgdir = 0;
  }
	p->sz = 0;
	p->pid = 0;
	p->parent = 0;
	p->name[0] = 0;
  p->tid = 0;
	p->killed = 0;
	p->state = UNUSED;
}

void
freeproc2(struct proc *p){
  int fd;
  for(fd = 0; fd < NOFILE; fd++){
    if(p->ofile[fd]){
      fileclose(p->ofile[fd]);
        p->ofile[fd] = 0;
    }
  }
  if(p->pgdir){
      deallocuvm(p->pgdir, p->sz, p->base);
		  p->pgdir = 0;
  }
	p->sz = 0;
	p->pid = 0;
	p->parent = 0;
	p->name[0] = 0;
	p->killed = 0;
  p->tid = 0;
	p->state = UNUSED;
}

int 
thread_create(thread_t *thread, void *(*start_routine)(void *), void *arg){
	struct proc *np;
  //Find master thread
  struct proc *curproc;
	uint ustack[2];
  struct proc *p;
  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(myproc()->pid == p->pid && p->tid == -1){
      curproc = p;
      break;
    }
  }
  release(&ptable.lock);

	if((np = allocproc(1)) == 0){
    freeproc(np);
		return -1;
	}

  *thread = np->tid;

	//Reference master_thread
	np->pgdir = curproc->pgdir;
	np->sz = curproc->sz;
  np->base = curproc->sz;
	*np->tf = *curproc->tf;
  np->parent = curproc;

	//Round up page for alignment
  uint stack_bottom = PGROUNDUP(np->sz);
  uint stack_sz = 2 * PGSIZE;
  uint stack_top = stack_bottom + stack_sz;

	//Allocate stack for new thread with a guard page
	if((np->sz = allocuvm(np->pgdir, stack_bottom, stack_top)) == 0){
		freeproc(np);
		return -1;
	}
  //하나의 thread가 추가되어 master_thread의 size는 증가
  curproc->sz += 2 * PGSIZE;

	//Set up guard page
	clearpteu(np->pgdir, (char *)(np->sz - 2*PGSIZE));

	np->tf->esp = np->sz - sizeof(ustack);
	//fake return PC
	ustack[0] = 0xffffffff;
	ustack[1] = (uint)arg;

	if(copyout(np->pgdir, np->tf->esp, ustack, sizeof(ustack)) < 0){
		freeproc(np);
    curproc->sz -= 2 *PGSIZE;
		return -1;
	}

	np->tf->eip = (uint)start_routine;
	//Reference to master thread

	//copy process file
	for(int i = 0; i < NOFILE; i++){
		if(curproc->ofile[i]){
			np->ofile[i] = filedup(curproc->ofile[i]);
		}
	}
	np->cwd = idup(curproc->cwd);
	//copy process name
	safestrcpy(np->name, curproc->name, sizeof(curproc->name));
	acquire(&ptable.lock);
	np->state = RUNNABLE;
	release(&ptable.lock);

	return 0;
}

int
sys_thread_create(void)
{
    thread_t *thread;
    void *(*start_routine)(void *);
    void *arg;

    if (argptr(0, (char **)&thread, sizeof(thread_t *)) < 0)
        return -1;
    if (argptr(1, (char **)&start_routine, sizeof(void *(*)(void *))) < 0)
        return -1;
    if (argptr(2, (char **)&arg, sizeof(void *)) < 0)
        return -1;

    return thread_create(thread, start_routine, arg);
}


void
thread_exit(void *retval){
	struct proc *curproc = myproc();
  struct proc *p;
	int fd;

	if(curproc == initproc){
		panic("init exiting");
	}
  if(retval){
    curproc->retval = retval;
  }

  // 파일 종료
	for(fd = 0; fd < NOFILE; fd++){
		if(curproc->ofile[fd]){
			fileclose(curproc->ofile[fd]);
			curproc->ofile[fd] = 0;
		}
	}

	begin_op();
	iput(curproc->cwd);
	end_op();
	curproc->cwd = 0;
  acquire(&ptable.lock);
	wakeup1(curproc->parent);

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->parent == curproc && !(curproc->tid == -1 && p->tid >= 0)){
      p->parent = initproc;
      if(p->state == ZOMBIE){
        wakeup1(initproc);
      }
    }
  }

	curproc->state = ZOMBIE;
	sched();
	panic("zombie exit");
}

int
sys_thread_exit(void)
{
    void *retval;

    if (argptr(0, (char **)&retval, sizeof(void *)) < 0)
        return -1;

    thread_exit(retval);
    return 0; 
}


int
thread_join(thread_t thread, void **retval){
	acquire(&ptable.lock);
	struct proc *curproc = myproc();
	struct proc *p;
  int found = 0;

	for(;;){
    found = 0;
		for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
			if(p->pid == curproc->pid && p->tid == thread){
        found = 1;
				if(p->state == ZOMBIE){
					if(retval){
						*retval = p->retval;
					}
					freeproc(p);
					release(&ptable.lock);
          // 스레드가 종료되었고 이의 retval를 회수했으면 종료
          return 0;
				}
			}
		}
    // 스레드를 찾지 못했거나 master thread가 kill 된경우 종료
    if(!found || curproc->killed){
      release(&ptable.lock);
      return -1;
    }
    // 스레드가 아직 종료되지 않은것이므로 종료되기까지 대기
    sleep(curproc, &ptable.lock);
	}
}

int
sys_thread_join(void)
{
    thread_t thread;
    void **retval;

    if (argint(0, (int *)&thread) < 0)
        return -1;
    if (argptr(1, (char **)&retval, sizeof(void **)) < 0)
        return -1;

    return thread_join(thread, retval);
}

void
delete_threads(struct proc *curproc){
  struct proc *p;
  struct proc *oldparent = curproc;
  acquire(&ptable.lock);
  if(curproc->tid != -1){
    oldparent = curproc->parent;
    curproc->parent = curproc->parent->parent;
    curproc->pgdir = copyuvm(curproc->parent->pgdir, curproc->parent->sz);
    curproc->sz = curproc->parent->sz;
    curproc->tid = -1;
  }
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == curproc->pid && p != curproc){
      if(p->tid == -1){
        p->killed = 1;
        continue;
      }
      freeproc(p);
    }
  }
  release(&ptable.lock);
}




