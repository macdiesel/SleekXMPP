"""
    SleekXMPP: The Sleek XMPP Library
    Copyright (C) 2010  Nathanael C. Fritz
    This file is part of SleekXMPP.

    See the file LICENSE for copying permission.
"""

import time
import threading
from threading import RLock
import logging
try:
    import queue
except ImportError:
    import Queue as queue


log = logging.getLogger(__name__)


class Task(object):

    """
    A scheduled task that will be executed by the scheduler
    after a given time interval has passed.

    Attributes:
        name     -- The name of the task.
        seconds  -- The number of seconds to wait before executing.
        callback -- The function to execute.
        args     -- The arguments to pass to the callback.
        kwargs   -- The keyword arguments to pass to the callback.
        repeat   -- Indicates if the task should repeat.
                    Defaults to False.
        qpointer -- A pointer to an event queue for queuing callback
                    execution instead of executing immediately.

    Methods:
        run   -- Either queue or execute the callback.
        reset -- Reset the task's timer.
    """

    def __init__(self, name, seconds, callback, args=None,
                 kwargs=None, repeat=False, qpointer=None):
        """
        Create a new task.

        Arguments:
            name     -- The name of the task.
            seconds  -- The number of seconds to wait before executing.
            callback -- The function to execute.
            args     -- The arguments to pass to the callback.
            kwargs   -- The keyword arguments to pass to the callback.
            repeat   -- Indicates if the task should repeat.
                        Defaults to False.
            qpointer -- A pointer to an event queue for queuing callback
                        execution instead of executing immediately.
        """
        self.name = name
        self.seconds = seconds
        self.callback = callback
        self.args = args or tuple()
        self.kwargs = kwargs or {}
        self.repeat = repeat
        self.next = time.time() + self.seconds
        self.qpointer = qpointer
        
    def run(self):
        """
        Execute the task's callback.

        If an event queue was supplied, place the callback in the queue;
        otherwise, execute the callback immediately.
        """
        if self.qpointer is not None:
            self.qpointer.put(('schedule', self.callback, self.args))
        else:
            self.callback(*self.args, **self.kwargs)
        self.reset()
        return self.repeat

    def reset(self):
        """
        Reset the task's timer so that it will repeat.
        """
        self.next = time.time() + self.seconds


class Scheduler(object):

    """
    A threaded scheduler that allows for updates mid-execution unlike the
    scheduler in the standard library.

    http://docs.python.org/library/sched.html#module-sched

    Attributes:
        addq        -- A queue storing added tasks.
        schedule    -- A list of tasks in order of execution times.
        thread      -- If threaded, the thread processing the schedule.
        run         -- Indicates if the scheduler is running.
        parentqueue -- A parent event queue in control of this scheduler.

    Methods:
        add     -- Add a new task to the schedule.
        process -- Process and schedule tasks.
        quit    -- Stop the scheduler.
    """

    def __init__(self, stopevent):
        """
        Create a new scheduler.

        Arguments:
            parentqueue -- A separate event queue controlling this scheduler.
        """
        self.addq = queue.Queue()
        self.schedule = []
        self.thread = None
        self.run = False
        self.stop = stopevent
        self.schedule_lock = RLock()

    def process(self, threaded=True):
        """
        Begin accepting and processing scheduled tasks.

        Arguments:
            threaded -- Indicates if the scheduler should execute in its own
                        thread. Defaults to True.
        """
        if threaded:
            self.thread = threading.Thread(name='scheduler_process',
                                           target=self._process)
            self.thread.daemon = True
            self.thread.start()
        else:
            self._process()

    def _process(self):
        """Process scheduled tasks."""
        self.run = True
        try:
            while self.run and not self.stop.isSet():
                wait = 1
                updated = False
                if self.schedule:
                    wait = self.schedule[0].next - time.time()
                try:
                    if wait <= 0.0:
                        newtask = self.addq.get(False)
                    else:
                        if wait >= 3.0:
                            wait = 3.0
                        newtask = self.addq.get(True, wait)
                except queue.Empty:
                    cleanup = []
                    self.schedule_lock.acquire()
                    for task in self.schedule:
                        if time.time() >= task.next:
                            updated = True
                            if not task.run():
                                cleanup.append(task)
                        else:
                            break
                    for task in cleanup:
                        x = self.schedule.pop(self.schedule.index(task))
                    
                else:
                    updated = True
                    self.schedule_lock.acquire()
                    self.schedule.append(newtask)
                finally:
                    if updated:
                        self.schedule = sorted(self.schedule,
                                               key=lambda task: task.next)
                    self.schedule_lock.release()
        except KeyboardInterrupt:
            self.run = False
        except SystemExit:
            self.run = False
        log.debug("Quitting Scheduler thread")
        

    def add(self, name, seconds, callback, args=None,
            kwargs=None, repeat=False, qpointer=None):
        """
        Schedule a new task.

        Arguments:
            name     -- The name of the task.
            seconds  -- The number of seconds to wait before executing.
            callback -- The function to execute.
            args     -- The arguments to pass to the callback.
            kwargs   -- The keyword arguments to pass to the callback.
            repeat   -- Indicates if the task should repeat.
                        Defaults to False.
            qpointer -- A pointer to an event queue for queuing callback
                        execution instead of executing immediately.
        """
        try:
            self.schedule_lock.acquire()
            for task in self.schedule:
                if task.name == name:
                    raise UniqueKeyConstraint("Key %s already exists" %name)
                
            self.addq.put(Task(name, seconds, callback, args,
                               kwargs, repeat, qpointer))
        except:
            raise
        finally:
            self.schedule_lock.release()
        
    def remove(self, name):
        try:
            self.schedule_lock.acquire()
            the_task = None
            for task in self.schedule:
                if task.name == name:
                    the_task = task
            if the_task is not None:
                self.schedule.remove(the_task)
        except:
            raise
        finally:
            self.schedule_lock.release()

    def quit(self):
        """Shutdown the scheduler."""
        self.run = False

class UniqueKeyConstraint(Exception):
    def __init__(self, value):
        self.parameter = value
    def __str__(self):
        return repr(self.parameter)