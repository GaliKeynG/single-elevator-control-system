#define FLOORS 10
#define TIMEOUT 20
#define MAX_CAP 5
#define STOP 0
#define UP 1
#define DOWN -1

// Global variables
int cur_floor = 1;
int dir = STOP;
int load = 0;
int target = -1; // -1 means no target

// Requests arrays (index 1 to 10)
bool req_up[FLOORS + 1];
bool req_down[FLOORS + 1];
bool req_inner[FLOORS + 1]; 

// Simple test sequence (0 means no input at that tick)
// Note: Manual initialization is safer in older Spin versions
int inputs[TIMEOUT + 1];

// Helper: Determine where to go next
// Logic: Simple linear scan 
inline update_target() {
    if
    :: (target == -1 || target == cur_floor) ->
        target = -1;
        i = 1; // Use process-local 'i'
        
        // Priority 1: Drop off passengers (Check inner requests)
        do
        :: (i <= FLOORS) ->
            if
            :: (req_inner[i]) -> 
                target = i; 
                goto found_target; // Jump out of loop
            :: else -> skip;
            fi;
            i++;
        :: (i > FLOORS) -> break;
        od;
        
        // Priority 2: Pick up new ones (Check outer requests)
        i = 1;
        do
        :: (i <= FLOORS) ->
            if
            :: (req_up[i] || req_down[i]) ->
                target = i;
                goto found_target;
            :: else -> skip;
            fi;
            i++;
        :: (i > FLOORS) -> break;
        od;

        found_target: skip; // Label to jump to
        
    :: else -> skip;
    fi;
}

// Helper: Read input sequence
inline read_input(t) {
    int f = inputs[t];
    if
    :: (f > 0 && f <= FLOORS) ->
        printf("DEBUG: Button pressed at floor %d\n", f);
        if
        :: (f < FLOORS) -> req_up[f] = 1;
        :: else -> req_down[f] = 1;
        fi;
    :: else -> skip;
    fi;
}

proctype elevator() {
    int t = 0;
    int i = 0; // Scratch variable for loops
    int dest = 0; // Temp variable for destination

    // Initialize inputs manually to avoid array syntax issues
    inputs[1] = 3; inputs[2] = 5; inputs[3] = 2; inputs[5] = 9; inputs[12] = 4;
    
    do
    :: (t >= TIMEOUT) -> 
        printf("Simulation finished.\n");
        break;
        
    :: (t < TIMEOUT) ->
        read_input(t);
        update_target();

        printf("T=%d | F:%d | Load:%d | Dest:%d | ", t, cur_floor, load, target);

        if
        :: (target == -1) -> 
            dir = STOP;
            printf("Idle\n");
            
        :: (target == cur_floor) ->
            printf("Open Door. ");
            
            // Someone gets out
            if
            :: (req_inner[cur_floor]) ->
                req_inner[cur_floor] = 0;
                if
                :: (load > 0) -> load--;
                :: else -> skip;
                fi;
                printf("Out. ");
            :: else -> skip;
            fi;
            
            // Someone gets in
            if
            :: (req_up[cur_floor] || req_down[cur_floor]) ->
                req_up[cur_floor] = 0;
                req_down[cur_floor] = 0;
                
                if
                :: (load < MAX_CAP) ->
                    load++;
                    // Sim: User goes to next floor + 2
                    dest = (cur_floor + 2); 
                    if
                    :: (dest > FLOORS) -> dest = 1;
                    :: else -> skip;
                    fi;
                    req_inner[dest] = 1; 
                    printf("In(to %d). ", dest);
                :: else -> 
                    printf("Full! ");
                fi;
            :: else -> skip;
            fi;
            
            printf("\n");
            target = -1; // Done here
            
        :: (target > cur_floor && target != -1) ->
            dir = UP;
            cur_floor++;
            printf("Going UP\n");
            
        :: (target < cur_floor && target != -1) ->
            dir = DOWN;
            cur_floor--;
            printf("Going DOWN\n");
        fi;
        
        t++;
    od;
}

init {
    printf("Elevator System Start (Cap: %d)\n", MAX_CAP);
    run elevator();
}
