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

// Simple test sequence
int inputs[TIMEOUT + 1];

// Helper: Determine where to go next
inline update_target() {
    // Only look for a new target if we don't have one or just arrived
    if
    :: (target == -1 || target == cur_floor) ->
        target = -1;
        i = 1; 
        
        // Priority 1: Check inner requests first
        do
        :: (i <= FLOORS) ->
            if
            :: (req_inner[i]) -> 
                target = i; 
                break; // Found one, stop looking
            :: else -> skip;
            fi;
            i++;
        :: (i > FLOORS) -> break;
        od;
        
        // Priority 2: Check outer requests (only if we didn't find an inner one)
        if
        :: (target == -1) ->
            i = 1;
            do
            :: (i <= FLOORS) ->
                if
                :: (req_up[i] || req_down[i]) ->
                    target = i;
                    break; // Found one, stop looking
                :: else -> skip;
                fi;
                i++;
            :: (i > FLOORS) -> break;
            od;
        :: else -> skip;
        fi;

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
    int i = 0;    
    int dest = 0; 

    // Manual input setup
    // writing line by line is easier to debug
    inputs[1] = 3; 
    inputs[2] = 5; 
    inputs[3] = 2; 
    inputs[5] = 9; 
    inputs[12] = 4;
    
    do
    :: (t < TIMEOUT) ->
        read_input(t);
        update_target();

        // Print status (simplified format)
        printf("Time %d: At %d, Load %d, Target %d\n", t, cur_floor, load, target);

        if
        :: (target == -1) -> 
            dir = STOP;
            printf("... Idle\n");
            
        :: (target == cur_floor) ->
            printf("... Door Open. ");
            
            // Unload
            if
            :: (req_inner[cur_floor]) ->
                req_inner[cur_floor] = 0;
                if
                :: (load > 0) -> load--;
                :: else -> skip;
                fi;
                printf("Unload. ");
            :: else -> skip;
            fi;
            
            // Load
            if
            :: (req_up[cur_floor] || req_down[cur_floor]) ->
                req_up[cur_floor] = 0;
                req_down[cur_floor] = 0;
                
                if
                :: (load < MAX_CAP) ->
                    load++;
                    // Logic: passenger goes to floor + 2
                    dest = (cur_floor + 2); 
                    if
                    :: (dest > FLOORS) -> dest = 1;
                    :: else -> skip;
                    fi;
                    req_inner[dest] = 1; 
                    printf("Load (dest %d). ", dest);
                :: else -> 
                    printf("Full! ");
                fi;
            :: else -> skip;
            fi;
            
            printf("\n");
            target = -1; 
            
        :: (target > cur_floor && target != -1) ->
            dir = UP;
            cur_floor++;
            printf("... Moving UP\n");
            
        :: (target < cur_floor && target != -1) ->
            dir = DOWN;
            cur_floor--;
            printf("... Moving DOWN\n");
        fi;
        
        t++;

    :: (t == TIMEOUT) -> 
        printf("Test Done.\n"); // Simple exit message
        break;
    od;
}

init {
    printf("Elevator System Start (Cap: %d)\n", MAX_CAP);
    run elevator();
}
