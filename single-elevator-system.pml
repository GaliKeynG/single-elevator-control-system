#define TOTAL_FLOORS 10
#define SIM_TIME 20
#define NO_REQ 99
#define MAX_LOAD  5

//Global status 
int current_floor = 1;
int moving_direction = 0;     //moving direction: 0 stop/1 up/-1 down
int door_is_open = 0;        //door status: 0 close/1 open
int current_load = 0；

//Mark which floor need to stop
int up_pending[TOTAL_FLOORS+1];
int down_pending[TOTAL_FLOORS+1];

//Request for the farthest floor
int farthest_up = 1;
int farthest_down = TOTAL_FLOORS;

//Testing sequence: SIM_TIME 20 
int incoming_requests[SIM_TIME+1] = {3, 5, 2, 1, 9, 99, 99, 99, 99, 99, 99, 99, 4};

#define QUEUE_SIZE 50
int queue[QUEUE_SIZE];
int front = 0；
int rear = 0;
int isempty = 0;

proctype elevator_control(){
    int clock =0;
    do
    :: (clock >= SIM_TIME) ->
    printf("TEST OVER\n");
    break;
    ::(clock < SIM_TIME) -> // do the current request first
    run handle_requests(clock);
    
    if 
    :: (next_target == -1) -> // if no request keep stay
    moving_direction = 0;
    door_is_open = 0;
    printf("Time%d: Elevator free, current floor%d\n", clock, current_floor);
    :: (next_target == current_floor) ->
    door_is_open = 1;
    printf("Time%d: Elevator stopby%dwhich floor\n", clock, current_floor);

    // do the request at current floor
    if (internal_request[current_floor] == 1){
        printf("do the inner request, passengers leave\n");
        internal_request[current_floor] = 0;
    }
    if (up_pending[current_floor] == 1){
        printf("do the up requests\n");
        up_pending[current_floor] = 0;
    }
    if (down_pending[current_floor] == 1){
        printf("do the down requests\n");
        down_pending[current_floor] = 0;
    }

    // MAX_LOAD checking, only in when is not MAX_LOAD
    if (current_load < MAX_LOAD){
        current_load++;
        printf("passengers in, current load%d%d\n", current_load, MAX_LOAD);
    }else {
        printf("Full load%d%d, reject new passengers\n", current_load, MAX_LOAD);

    }
    door_is_open = 0;
    printf("Close\n");
    ：：（next_target > current_floor）->
    current_floor++; //need to go up
    printf("Time%d: up to%dfloor (target:%dfloor)\n", clock, current_floor, next_target);
    moving direction = 1;
    ::(next_target < current_floor) ->
    current_floor--; //need to go down
    printf("Time%d: down to%dfloor(target:%dfloor)\n", clock, current_floor, next_target);
    moving_direction = -1;
    fi;

    clock++;
    od;

}

//system initialization
intit{
    //reset all requests to zero
    int i;
    for (i in internal_requests){internal_requests[i] = 0;}
    for (i in up_pending){up_pending[i] = 0;}
    for (i in down_pending){down_pending[i] = 0;}

    printf("Starting Elevator Control System (MAX LOAD: %d)", MAX_LOAD);
    run elevator_control();
}