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

// Property: Movement is only possible when the elevator's door is closed
pred elevatorOnlyMoveWhenDoorClosed[e: Elevator] {
	e.floor != e.floor' => e.door = Closed
}

test expect {
	-- TODO: test overall model properties here
	test1: {traces implies elevatorOnlyMoveWhenDoorClosed[Elevator]} for exactly 1 Elevator is theorem
	
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
