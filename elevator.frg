#lang forge/temporal

option max_tracelength 14

-- Do not change anything in this file!

/*---------------*\
|   Definitions   |
\*---------------*/
// See handout for detailed explanation of these sigs

sig Floor {
	above : lone Floor,
	below : lone Floor
}
one sig Top extends Floor {}
one sig Bottom extends Floor {}

abstract sig Door {}
one sig Open extends Door {}
one sig Closed extends Door {}

abstract sig Direction {}
one sig Up extends Direction {}
one sig Down extends Direction {}

sig Elevator {
	var floor : one Floor,
	var door : one Door,
	var requests : set Floor,
	var nextRequest : one Floor,  // nextRequest and lastMove fields only important 
	var lastMove: one Direction   // in procedures 4 and 5
}

pred floors {
	-- Enforcing top Floor
	no Top.above
	-- Enforcing bottom Floor
	no Bottom.below
	-- Floors are connected (could do via either top or bottom)
	all f : Floor | f in Bottom.*above
	-- Ensures above/below relations match up
	~above = below
}


/*-----------------------*\
|   Elevator Operations   |
\*-----------------------*/

pred init[e: Elevator] {
	-- The elevator starts on the bottom with its door closed
	e.floor = Bottom 
	e.door = Closed
	-- If there is a next request, it must be in the set of all requests
	-- Otherwise, nextRequest is Bottom by default
	some e.requests => {
		e.nextRequest in e.requests
	} else {
		e.nextRequest = Bottom
	}
	-- No lastMove in initial state: Just initialise to Up
	e.lastMove = Up
}

-- Conditions for the elevator to move up
pred moveUpEnabled[e: Elevator] {
    -- Cannot be on Top floor
	e.floor != Top
    -- Door must be closed
	e.door = Closed
}

-- Describes elevator moving up
pred moveUp[e: Elevator] {
    -- Meets guard conditions
	moveUpEnabled[e]
    -- Floor in next state is the floor above the current one
	e.floor' = e.floor.above
    -- Door is still closed
	e.door' = Closed
    -- Requests can be made, but cannot be resolved
	e.requests in e.requests'
    -- nextRequest cannot change
	e.nextRequest' = e.nextRequest
    -- lastMove is now Up
	e.lastMove' = Up
}

-- Conditions for the elevator to move down
pred moveDownEnabled[e: Elevator] {
    -- Cannot be on Bottom floor
	e.floor != Bottom
    -- Door must be closed
	e.door = Closed
}

-- Describes elevator moving down
pred moveDown[e: Elevator] {
    -- Meets guard conditions
	moveDownEnabled[e]
    -- Floor in next state is the floor below the current one
	e.floor' = e.floor.below
    -- Door is still closed
	e.door' = Closed
    -- Requests can be made, but cannot be resolved
	e.requests in e.requests'
    -- nextRequest cannot change
	e.nextRequest' = e.nextRequest
    -- lastMove is now Down
	e.lastMove' = Down
}

-- Conditions for elevator to open its door
pred openDoorEnabled[e: Elevator] {
    -- Floor should have been requested
	e.floor in e.requests
    -- Door should currently be closed
	e.door = Closed
}

-- Describes elevator opening its door
pred openDoor[e: Elevator] {
    -- Meets guard conditions
	openDoorEnabled[e]
    -- Floor cannot change
	e.floor' = e.floor
    -- Door should open
	e.door' = Open
    -- Nothing else can change
	e.requests' = e.requests
	e.nextRequest' = e.nextRequest
	e.lastMove' = e.lastMove
}

-- Conditions for elevator to pick up a passenger at a floor
pred pickUpEnabled[e: Elevator] {
    -- Door must be open
	e.door = Open
    -- The floor must be requested
	e.floor in e.requests
}

-- Describes elevator picking up a passenger
pred pickUp[e: Elevator] {
    -- Meets guard conditions
	pickUpEnabled[e]
    -- Door should close after pickup
	e.door' = Closed
    -- Floor should not change
	e.floor' = e.floor
    -- Requests for this floor should be resolved and
    -- new requests cannot be made
	e.requests' = e.requests - e.floor
	e.nextRequest = e.floor => {
		-- choose a new `nextRequest` if we have resolved the current one
		(some e.requests') => (e.nextRequest' in e.requests') else (e.nextRequest' = Bottom)
	} else {
        -- have not resolved the current request, do not change `nextRequest`
		e.nextRequest' = e.nextRequest
	}
    -- Elevator cannot move
	e.lastMove' = e.lastMove
}

-- Describes elevator staying still
pred stayStill[e: Elevator] {
    -- Floor stays the same
	e.floor' = e.floor
    -- Door is closed
	e.door' = Closed
    -- New requests can be made, but existing requests cannot be resolved
	e.requests in e.requests'
    -- Nothing else changes
	e.nextRequest' = e.nextRequest
	e.lastMove' = e.lastMove
}

-- All guard preds
pred enabled[e: Elevator] {
	moveUpEnabled[e] or 
	moveDownEnabled[e] or
	openDoorEnabled[e] or
	pickUpEnabled[e]
}

-- All "movement/action" preds
pred moves[e: Elevator] {
	moveUp[e] or
	moveDown[e] or
	openDoor[e] or
	pickUp[e]
}

-- Helper
pred pickUpCurIfRequesting[e: Elevator] {
	// if current floor is requesting and door is closed, open door
	(e.floor in e.requests) and (e.door = Closed) => openDoor[e]

	// if current floor is requesting and door is open, pick up
	// (pickUpEnabled encompasses both conditions)
	pickUpEnabled[e] => pickUp[e]
}

-- IMPORTANT: Defines reasonable floor and elevator logic
pred traces {
    -- Floors should have a reasonable structure
	floors
    -- If there are no requests, the nextRequest is Bottom by default
	all e: Elevator | always {(no e.requests) => e.nextRequest = Bottom}
    -- All elevators start obeying init
	all e: Elevator | init[e]
    -- All elevators either move or stayStill
	all e: Elevator | always {moves[e] or stayStill[e]}
}


/*-----------------------*\
|  5 Elevator Procedures  |
\*-----------------------*/

pred procedure1[e: Elevator] {
	// There are no requests if and only if the elevator is not moving 
	no e.requests iff stayStill[e]
	// putting priority of picking up request on the floor it is on
	always pickUpCurIfRequesting[e]
	// If there exists ANY requests below the current location means the elevator shall not move up
	some (e.floor.^below & e.requests) => not moveUp[e]
	// If there are no requests below the current floor, it shall not move down
	no (e.floor.^below & e.requests) => not moveDown[e]
}


pred procedure2[e: Elevator] {
	// The elevator is moving cont
	not stayStill[e]
	// it will pick up ppl on the way
	always pickUpCurIfRequesting[e]
	// Establishes that it can not move down until it is at the top, and it can not move up until it reaches the bottom
	// UNCERTAIN
	e.floor = Bottom => (not moveDown[e]) until e.floor = Top
	e.floor = Top => (not moveUp[e]) until e.floor = Bottom
}


pred procedure3[e: Elevator] {
	// Can't move  if there are no requests
	no e.requests iff stayStill[e]
	// Always pick up someone when there is a request on the current floor
 	always pickUpCurIfRequesting[e]
	// Ensure that requests in one direction stays consistent and does not change direction until all upward or downward requests are completed
	some (e.requests & e.floor.^above) => (not moveDown[e]) until no (e.requests & e.floor.^above)
	some (e.requests & e.floor.^below) => (not moveUp[e]) until no (e.requests & e.floor.^below)
}


pred procedure4[e: Elevator] {
	// Ensures same thing as before 
	no e.requests iff stayStill[e]

	always pickUpCurIfRequesting[e]
	// This enforces that we must complete each request individually to prevent completing multiple requests
	(e.nextRequest in e.floor.^above) => not moveDown[e] until (e.nextRequest not in e.floor.^above)
	(e.nextRequest in e.floor.^below) => not moveUp[e] until (e.nextRequest not in e.floor.^below)
	// If there is not next request, we default to go to the botoom
	(some e.requests) and (e.nextRequest not in e.requests) => e.nextRequest' in e.requests'
	((no e.requests) and (some e.requests')) => e.nextRequest' in e.requests'
}


pred procedure5[e: Elevator] {
	no e.requests iff stayStill[e]

	always pickUpCurIfRequesting[e]
	
	(e.nextRequest in e.floor.^above) => not moveDown[e] until (e.nextRequest not in e.floor.^above)
	(e.nextRequest in e.floor.^below) => not moveUp[e] until (e.nextRequest not in e.floor.^below)

	(some e.requests) and (e.nextRequest not in e.requests) => e.nextRequest' in e.requests'
	((no e.requests) and (some e.requests')) => e.nextRequest' in e.requests'
	// Once we reach a requested floor, we open
	pickUpEnabled[e] and (e.nextRequest = e.floor) => {
		// if last direction is up
		e.lastMove = Up => {
			// we will allow  and complete for new requests that are above
			some (e.requests' & e.floor.^above) => e.nextRequest' in (e.requests' & e.floor.^above)
		} else {
			// If the last direction is down, if there are new requests below, we complete taem
			some (e.requests' & e.floor.^below) => e.nextRequest' in (e.requests' & e.floor.^below)
		}
	}
}