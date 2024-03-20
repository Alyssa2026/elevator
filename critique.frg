#lang forge/temporal
-- Import all the elevator procedures to critique, along with
--   all of the sigs and predicates:
open "elevator.frg"


/*------------------------------------*\
|    Elevator Procedure Descriptions   |
\*------------------------------------*/

-- We provide the source code for 5 different procedures in elevator.frg. 
--   Based on the code and its comments, what documentation do you think would best describe each procedure? 
--   Think about the differences between the procedures and how to best communicate them. 

-- Procedure 1:
-- This procedure establishes when to not move
--  // The elevator should not move when there are no requests
	// This procedure puts priority of picking up request on the floor it is on
	// If there exists ANY requests below the current location means the elevator shall not move up
	// If there are no requests below the current floor, it shall not move down

-- Procedure 2:
--   This procedure describes continuous motion requirement of the elevator 
	// The elevator is moving continuously
	// it will pick up ppl on the way when there is a request at the current floor
	// Establishes that it can not move down until it is at the top, and it can not move up until it reaches the bottom

-- Procedure 3:
--  This ensures we will complete requests in one direction, and only swtich after one direction is completed 
	// Has the same initial requirements as 1,4,5 
	// Ensure that requests in one direction stays consistent and does not change direction until all upward or downward requests are completed

-- Procedure 4:
--   Enforces completing and adding each request individually 
	// Has the same initial requirements as 1,3,5 
	// This enforces that we must complete each request individually to prevent completing multiple requests
	// If there is not next request, we default to go to the botoom

-- Procedure 5:
--   Allow to complete current and new requests when already moving in that direction
	// Has the same initial requirements as 1,4,3
	// Once we reach a requested floor, we open
	// if last direction is up
		// we will allow  and complete for new requests that are above
		// If the last direction is down, if there are new requests below, we complete taem


/*------------------------------------*\
|    Model Properties + Verification   |
\*------------------------------------*/

-- TODO: encode a few predicates to test the properties of the overall model
--   and verify whether or not they hold in the following test-expect block

-- Hint: Think about what should / should not be possible for a typical elevator!

// Positive Preds
// Movement is only possible when the elevator's door is closed
pred elevatorOnlyMoveWhenDoorClosed[e: Elevator] {
	e.floor != e.floor' => e.door = Closed
}
// The elevator does not move when the door is open
pred elevatorDoesntOpenWhenMoving[e: Elevator] {
	e.door = Open => e.floor = e.floor'
}
// Goes to bottom where there are no requests
pred goToBottom[e: Elevator] {
 	e.requests =none => e.floor = Bottom
}
// The elevator door is closed and the elevator has not moved
pred elevatorDoesntMoveWhenDoorClosed[e: Elevator] {
	e.door = Closed and
	e.floor = e.floor'
}
// Property: Elevator doesn't move when there are no requests
pred elevatorDoesntMoveWithoutRequests[e: Elevator] {
	e.requests = none => e.floor = e.floor'
}

// Negative Preds
// The elevator is moving while the door is open 
pred elevatorMoveWhenDoorOpen[e: Elevator] {
	e.door = Open => e.floor != e.floor'
}
// The elevator is open with no requests
pred elevatorOpenWithNoRequest[e: Elevator] {
	e.door = Open
	e.requests = none
}
// The elevator is at the bottom but is going to move down
pred movingDownFromBottom[e: Elevator] {
	e.floor = Bottom and 
	e.floor'= e.floor.below
}
// The elevator is at the top but is going to move up
pred movingUpFromTop[e: Elevator] {
	e.floor = Top and 
	e.floor'= e.floor.above
}
// The elevator is at the top when there are no requests
pred atTop [e: Elevator] {
	e.floor = Top and
	e.requests=none
}

test expect {
	// Positive tests
	//  Movement is only possible when the elevator's door is closed
	test1: {traces implies elevatorOnlyMoveWhenDoorClosed[Elevator]} for exactly 1 Elevator is theorem
	// the elevator does not move when the door is open
	test2:{traces implies elevatorDoesntOpenWhenMoving[Elevator]} for exactly 1 Elevator is theorem
	// When there are no requests, the elevator goes to the bottom
	test3:{traces implies goToBottom[Elevator]} for exactly 1 Elevator is theorem
	// The door does not need to be constantly moving when the door is closed. However, this fails!
	// test4: { traces implies not elevatorDoesntMoveWhenDoorClosed[Elevator]} for exactly 1 Elevator is theorem
	// The elevator will not change floors when there are no requests 
	test5: {traces implies elevatorDoesntMoveWithoutRequests[Elevator]} for exactly 1 Elevator is sat

	// Negative tests
	// The door is open and moving is invalid
	test6:{traces and elevatorMoveWhenDoorOpen[Elevator]} for exactly 1 Elevator is sat
	// The door is open even though there are no requests, thus this not happening is sat
	test7: {traces and elevatorOpenWithNoRequest[Elevator]} for exactly 1 Elevator is unsat
	// The elevator is going to move down after it has reached the bottom floor is impossible
	test8: {traces and movingDownFromBottom[Elevator]} for exactly 1 Elevator is unsat
	// The elevator is going to move up after it has reached the top floor is impossible
	test9: {traces and movingUpFromTop[Elevator]} for exactly 1 Elevator is unsat
	// The elevator is not moving when there are requests is not expected 
	test10:{traces and atTop[Elevator]} for exactly 1 Elevator is unsat
}



/*-------------------------------------------------*\
|    Elevator Procedure Properties + Verification   |
\*-------------------------------------------------*/

-- TODO: encode a few predicates to test the properties of the 5 elevator procedures
--   and verify whether or not they hold in the following test-expect blocks. Remember
--   that procedures 4 and 5 make use of the `nextRequest` and `lastMove` Elevator
--   fields, so be sure to write predicates that test properties of these fields too.

-- Hint: Think about what behavior is allowed / expected by each procedure!

// Property: forward progress is always possible
//  Hint: `enabled` does not enforce that forward progress *happens* – just that it's possible.
pred forwardProgress[e: Elevator] {
	always eventually enabled[e]
}


test expect {
	-- TODO: test procedure1 properties here
	fp1: {traces and always procedure1[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem

}

test expect {
	-- TODO: test procedure2 properties here
	fp2: {traces and always procedure2[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem

}

test expect {
	-- TODO: test procedure3 properties here
	fp3: {traces and always procedure3[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem
}

test expect {
	-- TODO: test procedure4 properties here
	fp4: {traces and always procedure4[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem

}

test expect {
	-- TODO: test procedure5 properties here
	fp5: {traces and always procedure5[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem

}


/*-------------------------------------*\
|    Challenge Problem: Two Elevators   |
\*-------------------------------------*/

-- This predicate is meant to help test various procedures:
--   just change which procedure is being called here (in one place)
--   and the controller will follow suit.
-- You should focus on Procedure 5, but we have provided this in case you want
-- to try out the other procedures with multiple elevators!
pred runElevatorProcedure[e: Elevator] {
	procedure5[e]
}

-- The controller, depending on its own needs (which are incomprehensible to
--   mortals and people who work in the CIT) will allow some elevator(s) to go
--   in every state (but not necessarily all of them).
-- This predicate is needed for the challenge problem, but not sooner. 
pred elevatorControl {
	traces
	always {some e: Elevator | runElevatorProcedure[e]}
    always {all e: Elevator | not runElevatorProcedure[e] => stayStill[e]}
}

-- TODO: Multi-Elevator Fix
-- Add a constraint that ensures procedures work for multiple elevators. 



-- TODO: Procedure 5 Checks
-- Paste and edit your Procedure 5 checks here.
-- These should not all pass before you implement a multi-elevator fix,
-- and should pass after you include the fix. 
-- Note: When we say "pass", we mean that the tests that passed in the non-challenge
-- portion should pass, and those that failed previously should continue failing.
