"""
Student autograder utilities.

This file provides a common interface for the CS 61A project
student-side autograder. Students do not need to read or understand
the contents of this file.

Usage:
This file is intended to run as the main script. Test cases should
be defined in the faile 'tests.pkl'

This file supports the following primary options:

* Unlocking tests (-u): Students will receive test cases in locked
    form. Test cases can be unlocked by using the "-u" flag. Once a
    test is unlocked, students will be able to run the autograder with
    those cases (see below)
* Testing individual questions (-q): Students can test an individual
    question using the "-q" flag. Omitting the "-q" flag will test
    all unlocked test cases. By default, the autograder will stop once
    the first error is encountered (see below)
* Testing all questions regardless of errors (-a): When specified, the
    autograder continues running even if it encounters errors. The
    "-a" flag works even if the "-q" is used
* Interactive debugging (-i): by default, when the autograder
    encounters an error, it prints the stack trace and terminates. The
    "-i" will instead print the stack trace, then open an interactive
    console to allow students to inspect the environment.
* Adjusting the timeout limit (-t): specify the number of seconds
    before the autograder exits due to a timeout.
"""

import argparse
from code import InteractiveConsole, InteractiveInterpreter, compile_command
import re
import traceback
import os
import sys
import hmac
import pickle
import rlcompleter
import urllib.request
import pdb


######################
# PRINTING UTILITIES #
######################

def make_output_fns():
    """Returns functions related to printing output."""
    devnull = open(os.devnull, 'w')
    stdout = sys.stdout
    on = True
    def toggle_output(toggle_on=None):
        """Toggles output between stdout and /dev/null.

        PARAMTERS:
        toggle_on -- bool or None; if None, switch the output
                     destination; if True, switch output to stdout;
                     if False, switch output to /dev/null
        """
        nonlocal on
        if toggle_on is not None:
            on = not toggle_on
        if on:
            sys.stdout = devnull
        else:
            sys.stdout = stdout
        on = not on
    return toggle_output

toggle_output = make_output_fns()

def split(src, join=False):
    """Splits a (possibly multiline) string of Python input into
    a list, adjusting for common indents.

    PARAMETERS:
    src -- str; (possibly) multiline string of Python input
    join -- bool; if True, join output into one string

    DESCRIPTION:
    Indentation adjustment is determined by the first nonempty
    line. The characters of indentation for that line will be
    removed from the front of each subsequent line.

    RETURNS:
    list of strings; lines of Python input
    str; all lines combined into one string if join is True
    """
    src = src.lstrip('\n').rstrip()
    match = re.match('\s+', src)
    length = len(match.group(0)) if match else 0
    result = [line[length:] for line in src.split('\n')]
    if join:
        result = '\n'.join(result)
    return result

def underline(line, under='='):
    """Prints an underlined version of the given line with the
    specified underline style.

    PARAMETERS:
    line  -- str
    under -- str; a one-character string that specifies the underline
             style
    """
    print(line + '\n' + under * len(line))

def display_prompt(line, prompt='>>> '):
    """Formats and prints a given line as if it had been typed in an
    interactive interpreter.

    PARAMETERS:
    line   -- object; represents a line of Python code. If not a
              string, line will be converted using repr. Otherwise,
              expected to contain no newlines for aesthetic reasons
    prompt -- str; prompt symbol. If a space is desired between the
              symbol and input, prompt must contain the space itself
    """
    if type(line) != str:
        line = repr(line)
    print(prompt + line)

PS1 = '>>> '
PS2 = '... '

#####################
# TIMEOUT MECHANISM #
#####################

class TimeoutError(Exception):
    """Exception for timeouts."""
    _message = 'Evaluation timed out!'

    def __init__(self, timeout):
        """Constructor.

        PARAMTERS:
        timeout -- int; number of seconds before timeout error occurred
        """
        super().__init__(self)
        self.timeout = timeout

TIMEOUT = 10
def timed(fn, args=(), kargs={}, timeout=TIMEOUT):
    """Evaluates expr in the given frame.

    PARAMETERS:
    fn      -- function; Python function to be evaluated
    args    -- tuple; positional arguments for fn
    kargs   -- dict; keyword arguments for fn
    timeout -- int; number of seconds before timer interrupt

    RETURN:
    Result of calling fn(*args, **kargs).

    RAISES:
    TimeoutError -- if thread takes longer than timemout to execute
    Error        -- if calling fn raises an error, raise it
    """
    from threading import Thread
    class ReturningThread(Thread):
        """Creates a daemon Thread with a result variable."""
        def __init__(self):
            Thread.__init__(self)
            self.daemon = True
            self.result = None
            self.error = None
        def run(self):
            try:
                self.result = fn(*args, **kargs)
            except Exception as e:
                e._message = traceback.format_exc(limit=2)
                self.error = e
    submission = ReturningThread()
    submission.start()
    submission.join(timeout)
    if submission.is_alive():
        raise TimeoutError(timeout)
    if submission.error is not None:
        raise submission.error
    return submission.result

#####################
# Testing Mechanism #
#####################

class TestError(Exception):
    """Custom exception for autograder."""
    PREAMBLE = -1

    def __init__(self, case=None, frame=None):
        """Constructor.

        PARAMETERS:
        case  -- int; specifies the index of the case in the suite that
                 caused the error. If case == TestError.PREAMBLe,
                 denotes the preamble of the suite that cased the error
        frame -- dict; the global frame right before the error occurred
        """
        super().__init__()
        self.case = case
        self.frame = frame
        self.super_preamble = None

    def get(self, test, suite):
        """Gets the code that caused the error.

        PARAMTERS:
        test  -- dict; the test in which the error occurred
        suite -- int; the index of the suite in which the error
                 occurred

        RETURNS:
        str; the code that caused the error.
        """
        preamble = self.super_preamble + \
                   test.get('preamble', {}).get('all', '') + '\n' + \
                   test.get('preamble', {}).get(suite, '')
        preamble = split(preamble, join=True)
        if self.case == self.PREAMBLE:
            return preamble, ''

        assert 0 <= suite < len(test['suites']), 'Test {} does not have Suite {}'.format(get_name(test), suite)
        assert 0 <= self.case < len(test['suites'][suite]), 'Suite {} does not have Case {}'.format(suite, self.case)
        code, outputs, status = test['suites'][suite][self.case]
        code = split(code, join=True)
        return preamble + '\n' + code, outputs


def get_name(test):
    """Gets the name of a test.

    PARAMETERS:
    test -- dict; test cases for a question. Expected to contain a key
            'name', which either maps to a string or a iterable of
            strings (in which case the first string will be used)

    RETURNS:
    str; the name of the test
    """
    if type(test['name']) == str:
        return test['name']
    return test['name'][0]

def get_test(tests, question):
    """Retrieves a test for the specified question in the given list
    of tests.

    PARAMETERS:
    tests    -- list of dicts; list of tests
    question -- str; name of test

    RETURNS:
    dict; the test corresponding to question. If no such test is found,
    return None
    """
    for test in tests:
        if 'name' not in test:
            continue
        names = test['name']
        if type(names) == str:
            names = (names,)
        if question in names:
            return test


def run(test, global_frame=None, interactive=False, super_preamble=''):
    """Runs all test suites for this class.

    PARAMETERS:
    test         -- dict; test cases for a single question
    global_frame -- dict; bindings for the global frame
    interactive  -- bool; True if interactive mode is enabled
    super_preamble -- str; preamble that is executed for every test

    DESCRIPTION:
    Test suites should be correspond to the key 'suites' in test.
    If no such key exists, run as if zero suites are
    defined. Use the first value corresponding to the key 'name' in
    test as the name of the test.

    RETURNS:
    bool; True if all suites passed.
    """
    name = get_name(test)
    underline('Test ' + name)

    if global_frame is None:
        global_frame = {}
    if 'note' in test:
        print(split(test['note'], join=True))
    if 'suites' not in test:
        test['suites'] = []
    if 'cache' in test:
        try:
            cache = compile(split(test['cache'], join=True),
                            '{} cache'.format(name), 'exec')
            timed(exec, (cache, global_frame))
        except Exception as e:
            # TODO
            pass

    preamble = super_preamble
    if 'preamble' in test and 'all' in test['preamble']:
        preamble += test['preamble']['all']
    postamble = ''
    if 'postamble' in test and 'all' in test['postamble']:
        postamble = test['postamble']['all']

    passed = 0
    for counter, suite in enumerate(test['suites']):
        # Preamble and Postamble
        label = '{} suite {}'.format(name, counter)
        new_preamble = preamble
        if 'preamble' in test:
            new_preamble += test['preamble'].get(counter, '')
        new_preamble = compile(split(new_preamble, join=True),
                           '{} preamble'.format(label), 'exec')
        new_postamble = postamble
        if 'postamble' in test:
            new_postamble += test['postamble'].get(counter, '')
        new_postamble = compile(split(new_postamble, join=True),
                            '{} postamble'.format(label), 'exec')
        # TODO

        # Run tests
        toggle_output(False)
        try:
            frame = run_suite(new_preamble, suite, new_postamble, global_frame)
        except TestError as e:
            exec(new_postamble, e.frame)
            e.super_preamble = super_preamble
            toggle_output(True)
            frame = handle_failure(e, test, counter,
                                   global_frame.copy(), interactive)
            exec(new_postamble, frame)
            break
        else:
            passed += 1

    toggle_output(True)
    unlocked_cases = sum(1 if case[2] == 'unlocked' else 0
                         for suite in test['suites'] for case in suite)
    total_cases = sum(len(suite) for suite in test['suites'])

    if passed == len(test['suites']):
        print('All unlocked tests passed!')
    if unlocked_cases < total_cases:
        print('-- NOTE: {} still has {} locked cases! --'.format(name,
              total_cases - unlocked_cases))
    print()
    return passed == len(test['suites'])

def test_call(fn, args=(), kargs={}, case=-1, frame={}, exception=None):
    """Attempts to call fn with args and kargs. If a timeout or error
    occurs in the process, raise a TestError.

    PARAMTERS:
    fn    -- function
    args  -- tuple; positional arguments to fn
    kargs -- dict; keyword arguments to fn
    case  -- int; index of case to which the function call belongs
    frame -- dict; current state of the global frame

    RETURNS:
    result of calling fn

    RAISES:
    TestError; if calling fn causes an Exception or Timeout
    """
    try:
        result = timed(fn, args, kargs)
    except Exception as e:
        if type(exception)==type and issubclass(exception, BaseException) and isinstance(e, exception):
            return exception
        raise TestError(case, frame)
    else:
        return result


def run_suite(preamble, suite, postamble, global_frame):
    """Runs tests for a single suite.

    PARAMETERS:
    preamble     -- str; the preamble that should be run before
                    every test
    suite        -- list; each element is a test case, represented
                    as a 2-tuple or 3-tuple
    postamble    -- str; the postamble that should be run after every
                    test case
    global_frame -- dict; global frame

    DESCRIPTION:
    Each test case in the parameter suite is represented as a
    2-tuple

        (input, outputs)

    where:
    input       -- str; a (possibly multiline) string of Python
                   source code
    outputs     -- iterable or string; if string, outputs is the
                   sole expected output. If iterable, each element
                   in outputs should correspond to an input slot
                   in input (delimited by '$ ').

    For each test, a new frame is created and houses all bindings
    made by the test. The preamble will run first (if it exists)
    before the test input. The postamble will be run after the test.

    Expected output and actual output are tested on shallow equality
    (==). If a test fails, a TestError will be raised that
    contains information about the test.

    RETURNS:
    dict; the global frame to signal a success

    RAISES:
    TestError; contains information about the test that failed.
    """
    for case_num, (case, outputs, status) in enumerate(suite):
        if status == 'locked':
            continue
        frame = global_frame.copy()
        test_call(exec, (preamble, frame),
                  case=TestError.PREAMBLE, frame=frame)
        if type(outputs) == str:
            outputs = (outputs,)
        out_iter = iter(outputs)

        current, prompts = '', 0
        lines = split(case) + ['']
        for i, line in enumerate(lines):
            if line.startswith(' ') or compile_command(current.replace('$ ', '')) is None:
                current += line + '\n'
                continue

            if current.startswith('$ ') or \
                    (i == len(lines) - 1 and prompts == 0):
                expect = test_call(eval, (next(out_iter), frame.copy()),
                                   case=case_num, frame=frame)
                actual = test_call(eval, (current.replace('$ ', ''), frame),
                                   case=case_num, frame=frame,
                                   exception=expect)
                if expect != actual:
                    raise TestError(case_num, frame)
            else:
                test_call(exec, (current, frame), case=case_num,
                          frame=frame)
            current = ''
            if line.startswith('$ '):
                prompts += 1
            current += line + '\n'
        exec(postamble, frame)
    return global_frame

def handle_failure(error, test, suite_number, global_frame, interactive):
    """Handles a test failure.

    PARAMETERS:
    error        -- TestError; contains information about the
                    failed test
    test         -- dict; contains information about the test
    suite_number -- int; suite number (for informational purposes)
    global_frame -- dict; global frame
    interactive  -- bool; True if interactive mode is enabled

    DESCRIPTION:
    Expected output and actual output are checked with shallow
    equality (==).

    RETURNS:
    bool; True if error actually occurs, which should always be
    the case -- handle_failure should only be called if a test
    fails.
    """
    code_source, outputs = error.get(test, suite_number)
    underline('Test case failed:', under='-')
    try:
        compile(code_source.replace('$ ', ''),
               'Test {} suite {} case {}'.format(get_name(test), suite_number, error.case),
               'exec')
    except SyntaxError as e:
        print('SyntaxError:', e)
        return global_frame

    console = InteractiveConsole(locals=global_frame)

    if type(outputs) == str:
        outputs = (outputs,)
    out_iter = iter(outputs)

    current, prompts = '', 0
    lines = split(code_source) + ['']
    for i, line in enumerate(lines):
        if line.startswith(' ') or compile_command(current.replace('$ ', '')) is None:
            current += line + '\n'
            display_prompt(line.replace('$ ', ''), PS2)
            continue

        if current.startswith('$ ') or \
                (i == len(lines) - 1 and prompts == 0):
            try:
                expect = handle_test(eval, (next(out_iter), global_frame.copy()),
                                     console=console, current=current,
                                     interactive=interactive)
                actual = handle_test(eval, (current.replace('$ ', ''), global_frame),
                                     console=console, current=current,
                                     interactive=interactive,
                                     expect=expect)
            except TestError:
                return global_frame
            display_prompt(actual, '')

            if expect != actual:
                print('# Error: expected', repr(expect), 'got', repr(actual))
                if interactive:
                    interact(console)
                print()
                return global_frame
        else:
            try:
                handle_test(exec, (current, global_frame),
                            console=console, current=current,
                            interactive=interactive)
            except TestError:
                return global_frame
        current = ''

        if line.startswith('$ '):
            prompts += 1
        current += line + '\n'
        display_prompt(line.replace('$ ', ''), PS1)

    print()
    return global_frame

def handle_test(fn, args=(), kargs={}, console=None, current='',
                interactive=False, expect=None):
    """Handles a function call and possibly starts an interactive
    console.

    PARAMTERS:
    fn          -- function
    args        -- tuple; positional arguments to fn
    kargs       -- dict; keyword arguments to fn
    console     -- InteractiveConsole
    line        -- str; line that contained call to fn
    interactive -- bool; if True, interactive console will start upon
                   error

    RETURNS:
    result of calling fn

    RAISES:
    TestError if error occurs.
    """
    assert isinstance(console, InteractiveConsole), 'Missing interactive console'
    try:
        result = timed(fn, args, kargs)
    except RuntimeError:
        print('# Error: maximum recursion depth exceeded')
        if interactive:
            interact(console)
        print()
        raise TestError()
    except TimeoutError as e:
        print('# Error: evaluation exceeded {} seconds'.format(e.timeout))
        if interactive:
            interact(console)
        print()
        raise TestError()
    except Exception as e:
        if type(expect) == type and issubclass(expect, BaseException) and isinstance(e, expect):
            return expect
        stacktrace = traceback.format_exc()
        token = '<module>\n'
        index = stacktrace.rfind(token) + len(token)
        print('Traceback (most recent call last):')
        print(stacktrace[index:])
        print('# Error: expected', repr(expect), "got", e.__class__.__name__)
        if interactive:
            interact(console)
        print()
        raise TestError()
    else:
        return result

def interact(console):
    """Starts an interactive console.

    PARAMTERS:
    console -- InteractiveConsole
    """
    console.resetbuffer()
    console.interact('# Interactive console\n'
                     '# Type exit() to quit')


#######################
# UNLOCKING MECHANISM #
#######################

def run_preamble(preamble, frame):
    """Displays the specified preamble.

    PARAMETERS:
    preamble -- str
    frame    -- dict; global frame
    """
    console = InteractiveConsole(frame)
    incomplete = False
    for line in split(preamble):
        if not incomplete and not line:
            incomplete = False
            continue
        prompt = PS2 if incomplete else PS1
        display_prompt(line, prompt)
        incomplete = console.push(line)

def unlock(question, tests):
    """Unlocks a question, given locked_tests and unlocked_tests.

    PARAMETERS:
    question -- str; the name of the test
    tests    -- module; contains a list of locked tests

    DESCRIPTION:
    This function incrementally unlocks all cases in a specified
    question. Students must answer in the order that test cases are
    written. Once a test case is unlocked, it will remain unlocked.

    Persistant state is stored by rewriting the contents of
    tests.pkl. Students should NOT manually change these files.
    """
    hash_key = tests['project_info']['hash_key']
    imports = tests['project_info']['imports']

    test = get_test(tests['tests'], question)
    if test is None:
        print('Tests do not exist for "{}"'.format(question))
        print('Try one of the following:')
        print(map(get_name, tests['tests']))
        return
    name = get_name(test)

    prompt = '?'
    underline('Unlocking tests for {}'.format(name))
    print('At each "{}", type in what you would expect the output to be if you had implemented {}'.format(prompt, name))
    print('Type exit() to quit')
    print()

    global_frame = {}
    for line in imports:
        exec(line, global_frame)

    has_preamble = 'preamble' in test
    if has_preamble and 'all' in test['preamble']:
        run_preamble(test['preamble']['all'], global_frame)

    def hash_fn(x):
        return hmac.new(hash_key.encode('utf-8'),
                        x.encode('utf-8')).digest()

    if 'suites' not in test:
        return
    for suite_num, suite in enumerate(test['suites']):
        if not suite:
            continue
        if has_preamble and suite_num in test['preamble']:
            run_preamble(test['preamble'][suite_num],
                         global_frame.copy())
        for case in suite:
            if case[2] == 'unlocked':
                continue
            lines = split(case[0])
            answers = []
            outputs = case[1]
            if type(outputs) not in (list, tuple):
                outputs = [outputs]
            output_num = 0
            for line in lines:
                if len(lines) > 1 and not line.startswith('$'):
                    if line.startswith(' '): # indented
                        print(PS2 + line)
                    else:
                        print(PS1 + line)
                    continue
                line = line.replace('$ ', '')
                print(PS1 + line)
                correct = False
                while not correct:
                    try:
                        student_input = input(prompt + ' ')
                    except (KeyboardInterrupt, EOFError):
                        try:
                            print('\nExiting unlocker...')
                        # When you use Ctrl+C in Windows, it throws
                        # two exceptions, so you need to catch both of
                        # them.... aka Windows is terrible.
                        except (KeyboardInterrupt, EOFError):
                            pass
                        return
                    if student_input in ('exit()', 'quit()'):
                        print('\nExiting unlocker...')
                        return
                    correct = hash_fn(student_input) == outputs[output_num]
                    if not correct:
                        print("Not quite...try again!")
                answers.append(student_input)
                output_num += 1
            case[1] = answers
            case[2] = 'unlocked'

            print("Congratulations, you have unlocked this case!")
            print()

    print("You have unlocked all of the tests for this question!")

#########################
# AUTO-UPDATE MECHANISM #
#########################

def check_for_updates(tests):
    """Checks a remote url for changes to the project tests, and
    applies changes depending on user input.

    PARAMETERS:
    tests -- contents of tests.pkl

    RETURNS:
    bool; True if new changes were made, False if no changes made or
    error occurred.
    """
    version = tests['project_info']['version']
    remote = tests['project_info']['remote']
    print('You are running version', version, 'of the autograder')
    try:
        url = os.path.join(remote, 'CHANGES')
        data = timed(urllib.request.urlopen, (url,), timeout=5)
        changelog = data.read().decode('utf-8')
    except (urllib.error.URLError, urllib.error.HTTPError):
        print("Couldn't check remote autograder")
        return False
    except TimeoutError:
        print("Checking for updates timed out.")
        return False
    match = re.match('VERSION ([0-9.]+)', changelog)
    if match and match.group(1) != version:
        print('Version', match.group(1), 'is available.')
        prompt = input('Do you want to automatically download changes? [y/n]: ')
        if 'y' in prompt.lower():
            success = parse_changelog(tests, changelog, remote)
            return success
        else:
            print('Changes not made.')
    return False

def parse_changelog(tests, changelog, remote):
    """Parses a changelog and updates the tests with the specified
    changes.

    PARAMTERS:
    tests     -- dict; contents tests.pkl
    changelog -- str
    remote    -- str; url of remote files

    RETURNS:
    bool; True if updates successful
    """
    current_version = tests['project_info']['version']
    parts = changelog.partition('VERSION ' + current_version)
    if len(parts) == 3:     # If Version found
        changelog = parts[0]
    changes = re.split('VERSION ([0-9.]+)', changelog)
    changes = list(reversed(changes)) # most recent changes last
    changes.pop() # split will find empty string before first version
    assert len(changes) % 2 == 0
    num_changes = len(changes) // 2
    for i in range(num_changes):
        version = changes[2*i+1]
        change_header, change_contents = '', ''
        for line in changes[2*i].strip('\n').split('\n'):
            if line.startswith('    ') or line == '':
                change_contents += line[4:] + '\n'
                continue
            if change_header != '':
                try:
                    apply_change(change_header, change_contents, tests,
                                 remote)
                except AssertionError as e:
                    print("Update error:", e)
                    return False
            change_header = line
            change_contents = ''
        # Apply last change
        try:
            terminate = apply_change(change_header, change_contents, tests, remote)
        except AssertionError as e:
            print("Update error:", e)
            return False
        if terminate:
            break
            tests['project_info']['version'] = version

    toggle_output(True)
    tests['project_info']['version'] = version
    print("Updated to VERSION " + version)
    if version != changes[-1]:
        print("Please re-run the autograder to check for further "
              "updates")
    else:
        print("Applied changelog:\n")
        print(changelog)
    toggle_output(False)
    return True

CHANGE = 'CHANGE'
APPEND = 'APPEND'
REMOVE = 'REMOVE'
GRADER = 'GRADER'

def apply_change(header, contents, tests, remote):
    """Subroutine that applies the changes described by the header
    and contents.

    PARAMTERS:
    header   -- str; a line describing the type of change
    contents -- str; contents of change, if applicable
    tests    -- dict; contents of tests.pkl

    RAISES:
    AssertionError; if any invalid changes are attempted.

    RETURNS:
    bool; True if GRADER was updated, in which case update should
    exit immediately
    """
    error_msg = 'invalid change "{}"'.format(header)
    if header.strip() == GRADER:
        try:
            url = os.path.join(remote, 'autograder.py')
            data = timed(urllib.request.urlopen, (url,), timeout=5)
            new_autograder = data.read().decode('utf-8')
        except (urllib.error.URLError, urllib.error.HTTPError):
            raise AssertionError("Couldn't retrive remote update for autograder.py")
        except TimeoutError:
            raise AssertionError("Checking for updates timed out.")
        with open('autograder.py', 'w') as f:
            f.write(new_autograder)
        return True

    header = header.split('::')
    assert len(header) == 3, error_msg

    change_type = header[0].strip()
    if 'test' in header[1]:
        test_name = header[1].replace('test', '').strip()
        test = get_test(tests['tests'], test_name)
        target = "test"
    else:
        target = "tests['" + header[1].strip() + "']"
    target += header[2].strip()

    assert target is not None, 'Invalid test to update: {}'.format(test_name)

    if change_type == CHANGE:
        update = "{} = {}".format(target, contents)
    elif change_type == APPEND:
        update = "{}.append({})".format(target, contents)
    elif change_type == REMOVE:
        assert contents == '', "Tried " + REMOVE + " with nonempty contents: " + contents
        update = "del {}".format(target)
    else:
        raise(error_msg)
    try:
        exec(update)
    except Exception as e:
        raise AssertionError(e.__class__.__name__ + ": " + str(e) + ": " + update)

##########################
# COMMAND-LINE INTERFACE #
##########################

def run_all_tests():
    """Runs a command line interface for the autograder."""
    parser = argparse.ArgumentParser(description='CS61A autograder')
    parser.add_argument('-u', '--unlock', type=str, 
                        help='Unlocks the specified question')
    parser.add_argument('-q', '--question', type=str,
                        help='Run tests for the specified question')
    parser.add_argument('-a', '--all', action='store_true',
                        help='Runs all tests, regardless of failures')
    parser.add_argument('-i', '--interactive', action='store_true',
                        help='Enables interactive mode upon failure')
    parser.add_argument('-t', '--timeout', type=int,
                        help='Change timeout length')
    args = parser.parse_args()

    with open('tests.pkl', 'rb') as f:
        all_tests = pickle.load(f)

    new = check_for_updates(all_tests)
    if new:
        with open('tests.pkl', 'wb') as f:
            pickle.dump(all_tests, f, pickle.DEFAULT_PROTOCOL)
        exit(0)
    print()

    if args.unlock:
        unlock(args.unlock, all_tests)

        with open('tests.pkl', 'wb') as f:
            pickle.dump(all_tests, f, pickle.DEFAULT_PROTOCOL)
    else:
        if args.question:
            tests = get_test(all_tests['tests'], args.question)
            if not tests:
                print('Test {} does not exist'.format(args.question))
                exit(1)
            tests = [tests]
        else:
            tests = all_tests['tests']

        if args.timeout:
            global TIMEOUT
            TIMEOUT = args.timeout

        global_frame = {}
        for line in all_tests['project_info']['imports']:
            exec(line, global_frame)
        exec(split(all_tests.get('cache', ''), join=True), global_frame)
        for test in tests:
            passed = run(test, global_frame, args.interactive, all_tests['preamble'])
            if not args.all and not passed:
                return
        underline('Note:', under='-')
        print("""Remember that the tests in this autograder are not exhaustive, so try your own tests in the interpreter!""")


if __name__ == '__main__':
    run_all_tests()
