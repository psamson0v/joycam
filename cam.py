# Point-and-shoot camera for Raspberry Pi w/camera and Adafruit PiTFT.
# This must run as root (sudo python cam.py) due to framebuffer, etc.
#
# Adafruit invests time and resources providing this open source code,
# please support Adafruit and open-source development by purchasing
# products from Adafruit, thanks!
#
# http://www.adafruit.com/products/998  (Raspberry Pi Model B)
# http://www.adafruit.com/products/1367 (Raspberry Pi Camera Board)
# http://www.adafruit.com/products/1601 (PiTFT Mini Kit)
# This can also work with the Model A board and/or the Pi NoIR camera.
#
# Prerequisite tutorials: aside from the basic Raspbian setup and
# enabling the camera in raspi-config, you should configure WiFi (if
# using wireless with the Dropbox upload feature) and read these:
# PiTFT setup (the tactile switch buttons are not required for this
# project, but can be installed if you want them for other things):
# http://learn.adafruit.com/adafruit-pitft-28-inch-resistive-touchscreen-display-raspberry-pi
# Dropbox setup (if using the Dropbox upload feature):
# http://raspi.tv/2013/how-to-use-dropbox-with-raspberry-pi
#
# Written by Phil Burgess / Paint Your Dragon for Adafruit Industries.
# BSD license, all text above must be included in any redistribution.

import atexit
import _pickle as pickle
import errno
import fnmatch
import io
import os
import os.path
from picamera2 import Picamera2
import pygame
import stat
import threading
import time
import cv2
from pygame.locals import *
from subprocess import call
import queue
import math
from enum import Enum
from libcamera import controls


def fitBlit(rect, bitmap, screen, smooth=False):
    if bitmap is None:
        return

    scaledWidth = bitmap.get_width() / rect[2]
    scaledHeight = bitmap.get_height() / rect[3]
    scaleFactor = max(scaledWidth, scaledHeight)
    if smooth:
        transformed = pygame.transform.smoothscale(bitmap, (int(
            bitmap.get_width() / scaleFactor), int(bitmap.get_height() / scaleFactor)))
    else:
        transformed = pygame.transform.scale(bitmap, (int(
            bitmap.get_width() / scaleFactor), int(bitmap.get_height() / scaleFactor)))

    screen.blit(transformed,
                (int(rect[0] + (rect[2] - bitmap.get_width() / scaleFactor) / 2),
                 int(rect[1] + (rect[3] - bitmap.get_height() / scaleFactor) / 2)))


def fillBlit(rect, bitmap, screen, smooth=False):
    if bitmap is None:
        return

    scaledWidth = bitmap.get_width() / rect[2]
    scaledHeight = bitmap.get_height() / rect[3]
    scaleFactor = min(scaledWidth, scaledHeight)
    if smooth:
        transformed = pygame.transform.smoothscale(bitmap, (int(
            bitmap.get_width() / scaleFactor), int(bitmap.get_height() / scaleFactor)))
    else:
        transformed = pygame.transform.scale(bitmap, (int(
            bitmap.get_width() / scaleFactor), int(bitmap.get_height() / scaleFactor)))

    screen.blit(transformed,
                (int(rect[0] + (rect[2] - bitmap.get_width() / scaleFactor) / 2),
                 int(rect[1] + (rect[3] - bitmap.get_height() / scaleFactor) / 2)))


# UI classes ---------------------------------------------------------------

# Small resistive touchscreen is best suited to simple tap interactions.
# Importing a big widget library seemed a bit overkill.  Instead, a couple
# of rudimentary classes are sufficient for the UI elements:

# Icon is a very simple bitmap class, just associates a name and a pygame
# image (PNG loaded from icons directory) for each.
# There isn't a globally-declared fixed list of Icons.  Instead, the list
# is populated at runtime from the contents of the 'icons' directory.


class Icon:

    def __init__(self, name):
        self.name = name
        try:
            self.bitmap = pygame.image.load(iconPath + '/' + name + '.png')
        except BaseException:
            pass

# Button is a simple tappable screen region.  Each has:
#  - bounding rect ((X,Y,W,H) in pixels)
#  - optional background color and/or Icon (or None), always centered
#  - optional foreground Icon, always centered
#  - optional single callback function
#  - optional single value passed to callback
# Occasionally Buttons are used as a convenience for positioning Icons
# but the taps are ignored.  Stacking order is important; when Buttons
# overlap, lowest/first Button in list takes precedence when processing
# input, and highest/last Button is drawn atop prior Button(s).  This is
# used, for example, to center an Icon by creating a passive Button the
# width of the full screen, but with other buttons left or right that
# may take input precedence (e.g. the Effect labels & buttons).
# After Icons are loaded at runtime, a pass is made through the global
# buttons[] list to assign the Icon objects (from names) to each Button.


class Button:

    def __init__(self, rect, **kwargs):
        self.rect = rect  # Bounds
        self.color = None  # Background fill color, if any
        self.iconBg = None  # Background Icon (atop color fill)
        self.iconFg = None  # Foreground Icon (atop background)
        self.bg = None  # Background Icon name
        self.fg = None  # Foreground Icon name
        self.callback = None  # Callback function
        self.value = None  # Value passed to callback
        for key, value in kwargs.items():
            if key == 'color':
                self.color = value
            elif key == 'bg':
                self.bg = value
            elif key == 'fg':
                self.fg = value
            elif key == 'cb':
                self.callback = value
            elif key == 'value':
                self.value = value

    def selected(self, pos):
        x1 = self.rect[0]
        y1 = self.rect[1]
        x2 = x1 + self.rect[2] - 1
        y2 = y1 + self.rect[3] - 1
        if ((pos[0] >= x1) and (pos[0] <= x2) and
                (pos[1] >= y1) and (pos[1] <= y2)):
            if self.callback:
                if self.value is None:
                    self.callback()
                else:
                    self.callback(self.value)
            return True
        return False

    def draw(self, screen):
        if self.color:
            screen.fill(self.color, self.rect)
        if self.iconBg:
            fitBlit(self.rect, self.iconBg.bitmap, screen)
        if self.iconFg:
            fitBlit(self.rect, self.iconFg.bitmap, screen)

    def setBg(self, name):
        if name is None:
            self.iconBg = None
        else:
            for i in icons:
                if name == i.name:
                    self.iconBg = i
                    break


class Screen(Enum):
    REFRESH = -1 # Fake screen mode to force a referesh
    VIEW = 0
    DELETE = 1
    NO_IMG = 2
    VIEWFINDER = 3
    SETTINGS_STORAGE = 4
    SETTINGS_SIZE = 5
    SETTINGS_EFFECT = 6
    SETTINGS_ISO = 7
    SETTINGS_EV = 8
    QUIT = 9

class ZoomMode(Enum):
    NORMAL = 0 # full sensor displayed
    ZOOMED = 1 # extreme zoom to help focus, not intended to take photos


# UI callbacks -------------------------------------------------------------
# These are defined before globals because they're referenced by items in
# the global buttons[] list.

def isoCallback(n):  # Pass 1 (next ISO) or -1 (prev ISO)
    global isoMode
    setIsoMode((isoMode + n) % len(isoData))


def evCallback(n):  # Pass 1 (next ISO) or -1 (prev ISO)
    global evMode
    setEvMode((evMode + n) % len(evData))


def settingCallback(n):  # Pass 1 (next setting) or -1 (prev setting)
    global screenMode
    # Omitting Storage settings because it doesn't do anything
    # Omitting Effect settings because it doesn't do anything
    # Omitting Delete Confirmation and No Image because those are special screens you can't navigate to normally
    acceptableModes = (Screen.VIEW, Screen.VIEWFINDER, Screen.SETTINGS_EV,
                       Screen.SETTINGS_ISO, Screen.SETTINGS_SIZE, Screen.QUIT)

    # You can't navigate out of these normally
    if screenMode not in acceptableModes:
        return

    position = acceptableModes.index(screenMode)
    position += n
    position %= len(acceptableModes)
    screenMode = acceptableModes[position]


def fxCallback(n):  # Pass 1 (next effect) or -1 (prev effect)
    global fxMode
    setFxMode((fxMode + n) % len(fxData))


def quitCallback():  # Quit confirmation button
    saveSettings()
    raise SystemExit


def viewCallback(n):  # Viewfinder buttons
    global loadIdx, scaled, screenMode, screenModePrior, settingMode, storeMode

    if n == 0:   # Gear icon (settings)
        screenMode = Screen(settingMode)  # Switch to last settings mode
    elif n == 1:  # Play icon (image playback)
        if scaled:  # Last photo is already memory-resident
            loadIdx = saveIdx
            screenMode = Screen.VIEW  # Image playback
            screenModePrior = Screen.REFRESH  # Force screen refresh
        else:      # Load image
            r = imgRange(pathData[storeMode])
            if r:
                showImage(r[1])  # Show last image in directory
            else:
                screenMode = Screen.NO_IMG  # No images
    else:  # Rest of screen = shutter
        takePicture()


def doneCallback():  # Exit settings
    global screenMode, settingMode
    if screenMode.value > 3:
        settingMode = screenMode.value
        saveSettings()
    screenMode = Screen.VIEWFINDER  # Switch back to viewfinder mode

def zoomModeCallback():
    global zoom_mode
    print('zooming')
    if zoom_mode == ZoomMode.NORMAL:
        zoom_mode = ZoomMode.ZOOMED
        print('zoomed in')
    else:
        zoom_mode = ZoomMode.NORMAL
        print('zoomed out')
    setZoomMode(zoom_mode)


screen = None  # Ugly hack to get the image viewer to load well


def spinner():
    global busy, screenMode, screenModePrior, screen

    # screen is not ready
    if not screen:
        return
    buttons.get(screenMode)[3].setBg('working')
    buttons.get(screenMode)[3].draw(screen)
    pygame.display.update()

    busy = True
    n = 0
    while busy is True:
        buttons.get(screenMode)[4].setBg('work-' + str(n))
        buttons.get(screenMode)[4].draw(screen)
        pygame.display.update()
        n = (n + 1) % 5
        time.sleep(0.15)

    buttons.get(screenMode)[3].setBg(None)
    buttons.get(screenMode)[4].setBg(None)
    screenModePrior = Screen.REFRESH  # Force refresh


def imgRange(path):
    min = 9999
    max = 0
    try:
        for file in os.listdir(path):
            if fnmatch.fnmatch(file, 'IMG_[0-9][0-9][0-9][0-9].JPG'):
                i = int(file[4:8])
                if (i < min):
                    min = i
                if (i > max):
                    max = i
    finally:
        return None if min > max else (min, max)


def showNextImage(direction):
    global busy, loadIdx

    t = threading.Thread(target=spinner)
    t.start()

    try:
        n = loadIdx
        while True:
            n += direction
            if (n > 9999):
                n = 0
            elif (n < 0):
                n = 9999
            if os.path.exists(pathData[storeMode] + '/IMG_' + '%04d' % n + '.JPG'):
                showImage(n)
                break
    except:
        # TODO: show an error message
        pass

    busy = False
    t.join()


def showImage(n):
    global busy, loadIdx, scaled, screenMode, screenModePrior, sizeMode, storeMode

    t = threading.Thread(target=spinner)
    t.start()

    img = pygame.image.load(
        pathData[storeMode] + '/IMG_' + '%04d' % n + '.JPG')
    scaled = pygame.transform.scale(img, sizeData[sizeMode][1])
    loadIdx = n

    busy = False
    t.join()

    screenMode = Screen.VIEW  # Photo playback
    screenModePrior = Screen.REFRESH  # Force screen refresh


def imageCallback(n):  # Pass 1 (next image), -1 (prev image) or 0 (delete)
    global screenMode
    if n == 0:
        screenMode = Screen.DELETE  # Delete confirmation
    else:
        showNextImage(n)


def deleteCallback(n):  # Delete confirmation
    global loadIdx, scaled, screenMode, screenModePrior, storeMode

    # Program returning to delete screen? Not inited yet
    if not screen:
        return

    screenMode = Screen.VIEW
    screenModePrior = Screen.REFRESH
    if n is True:
        os.remove(pathData[storeMode] + '/IMG_' + '%04d' % loadIdx + '.JPG')
        if (imgRange(pathData[storeMode])):
            screen.fill(0)
            pygame.display.update()
            showNextImage(-1)
        else:  # Last image deleteted; go to 'no images' mode
            screenMode = Screen.NO_IMG
            scaled = None
            loadIdx = -1


def storeModeCallback(n):  # Radio buttons on storage settings screen
    global storeMode
    buttons.get(Screen.SETTINGS_STORAGE)[storeMode + 3].setBg('radio3-0')
    storeMode += n
    storeMode %= len(sizeData)
    buttons.get(Screen.SETTINGS_STORAGE)[storeMode + 3].setBg('radio3-1')

# This is split into two methods since when loading the settings we just want to init button state, not apply settings
def setSizeModeAndButtons(n):
    global sizeMode
    # Size mode should never be out of bounds, but it might be!
    buttons.get(Screen.SETTINGS_SIZE)[sizeMode + 3].setBg('radio3-0')
    sizeMode = n
    buttons.get(Screen.SETTINGS_SIZE)[sizeMode + 3].setBg('radio3-1')

def setSizeMode(n):
    setSizeModeAndButtons(n)
    camera.still_configuration.main.size = sizeData[n][0]
    camera.stop()
    camera.configure("still")
    camera.still_configuration.align()
    camera.start()
    setZoomMode(ZoomMode.NORMAL) #reset zoom


def sizeModeCallback(n):  # Radio buttons on size settings screen
    global sizeMode
    setSizeMode((sizeMode + n) % len(sizeData))


# Global stuff -------------------------------------------------------------
screenMode = Screen.VIEWFINDER      # Current screen mode; default = viewfinder
screenModePrior = Screen.REFRESH      # Prior screen mode (for detecting changes)
settingMode = 4      # Last-used settings mode (default = storage)
storeMode = 0      # Storage mode; default = Photos folder
storeModePrior = -1      # Prior storage mode (for detecting changes)
sizeMode = 0      # Image size: default = Large
fxMode = 0      # Image effect: default = Normal
isoMode = 0      # ISO setting; default = Auto
evMode = 0       # EV Compensation. Default: 0
iconPath = 'icons'  # Subdirectory containing UI bitmaps (PNG format)
saveIdx = -1      # Image index for saving (-1 = none set yet)
loadIdx = -1      # Image index for loading
scaled = None    # pygame Surface w/last-loaded image
screen_height = 240     # TFT display height
screen_width = 240     # TFT display width
# counterclockwise rotation of your camera sensor from vertical (ribbon cable port pointing down)
screen_rotation = 270
imageQueue = queue.Queue()
zoom_mode = ZoomMode.NORMAL # By default digital zoom is not used

sizeData = [  # Camera parameters for different size settings
    # Full res      Viewfinder
    [(4000, 3000), (320, 240)],  # 12 MP
    [(3840, 2160), (426, 240)],  # 8 MP / 4K HD
    [(2592, 1944), (320, 240)],  # 5 MP
]

isoData = [  # Values for ISO settings [ISO value, indicator X position]
    [0, 27], [100, 64], [200, 97], [320, 137],
    [400, 164], [500, 197], [640, 244], [800, 297]]

evData = [  # Values for EV compensation settings [EV compensation value, indicator X position]
    [-8, 13],
    [-7, int(13+18.5)],
    [-6, int(13+18.5*2)],
    [-5, int(13+18.5*3)],
    [-4, int(13+18.5*4)],
    [-3, int(13+18.5*5)],
    [-2, int(13+18.5*6)],
    [-1, int(13+18.5*7)],
    [0,  int(13+18.5*8)],
    [1,  int(13+18.5*9)],
    [2,  int(13+18.5*10)],
    [3,  int(13+18.5*11)],
    [4,  int(13+18.5*12)],
    [5,  int(13+18.5*13)],
    [6,  int(13+18.5*14)],
    [7,  int(13+18.5*15)],
    [8,  int(13+18.5*16)]
]

# A fixed list of image effects is used (rather than polling
# camera.IMAGE_EFFECTS) because the latter contains a few elements
# that aren't valid (at least in video_port mode) -- e.g. blackboard,
# whiteboard, posterize (but posterise, British spelling, is OK).
# Others have no visible effect (or might require setting add'l
# camera parameters for which there's no GUI yet) -- e.g. saturation,
# colorbalance, colorpoint.
fxData = [
    'none', 'sketch', 'gpen', 'pastel', 'watercolor', 'oilpaint', 'hatch',
    'negative', 'colorswap', 'posterise', 'denoise', 'blur', 'film',
    'washedout', 'emboss', 'cartoon', 'solarize']

pathData = [
    '/home/pi/Photos',     # Path for storeMode = 0 (Photos folder)
    '/boot/DCIM/CANON999',  # Path for storeMode = 1 (Boot partition)
    '/home/pi/Photos']     # Path for storeMode = 2 (Dropbox)

icons = []  # This list gets populated at startup

# buttons[] is a dict of lists; each top-level element corresponds
# to one screen mode (e.g. viewfinder, image playback, storage settings),
# and each element within those lists corresponds to one UI button.
# There's a little bit of repetition (e.g. prev/next buttons are
# declared for each settings screen, rather than a single reusable
# set); trying to reuse those few elements just made for an ugly
# tangle of code elsewhere.

# Scaling button sized dynamically to screen resolution.
# The old camera project hardcoded these to fit 320x240


def scaleHeight(height):
    return int(height * screen_height / 240)


def scaleWidth(width):
    return int(width * screen_width / 320)


buttons = dict({
    # Screen mode 0 is photo playback
    Screen.VIEW: [Button((0, scaleWidth(188), screen_width, scaleHeight(52)), ),  # We don't need the done button anymore, but the layout is hardcoded
                  Button((0, 0, scaleWidth(80), scaleHeight(52)), bg='prev', cb=imageCallback, value=-1),
                  Button((scaleWidth(240), 0, scaleWidth(80), scaleHeight(52)), bg='next', cb=imageCallback, value=1),
                  Button((scaleWidth(88), scaleHeight(70), scaleWidth(157),
                          scaleHeight(102))),  # 'Working' label (when enabled)
                  Button((scaleWidth(148), scaleHeight(129), scaleWidth(
                      22), scaleHeight(22))),  # Spinner (when enabled)
                  Button((scaleWidth(121), 0, scaleWidth(78), scaleHeight(52)), bg='trash', cb=imageCallback, value=0)],

    # Screen mode 1 is delete confirmation
    Screen.DELETE: [Button((0, scaleHeight(35), scaleWidth(320), scaleHeight(33)), bg='delete'),
                    Button((scaleWidth(32), scaleHeight(86), scaleWidth(120), scaleHeight(100)), bg='yn', fg='yes',
                           cb=deleteCallback, value=True),
                    Button((scaleWidth(168), scaleHeight(86), scaleWidth(120), scaleHeight(100)), bg='yn', fg='no',
                           cb=deleteCallback, value=False)],

    # Screen mode 2 is 'No Images'
    Screen.NO_IMG: [Button((0, 0, scaleWidth(320), scaleHeight(240)), cb=doneCallback),  # Full screen = button
                    # Button((0, scaleHeight(188), scaleWidth(320), scaleHeight(52)),
                    # bg='done'),       # Fake 'Done' button
                    Button((0, scaleHeight(53), scaleWidth(320), scaleHeight(80)), bg='empty')],     # 'Empty' message

    # Screen mode 3 is viewfinder / snapshot
    Screen.VIEWFINDER: [Button((0, scaleHeight(188), scaleWidth(156), scaleHeight(52)), bg='gear', cb=viewCallback, value=0),
                        Button((scaleWidth(164), scaleHeight(188), scaleWidth(156),
                                scaleHeight(52)), bg='play', cb=viewCallback, value=1),
                        Button((0, 0, scaleWidth(320), scaleHeight(240)),
                               cb=viewCallback, value=2),
                        Button((scaleWidth(88), scaleHeight(51), scaleWidth(157),
                                scaleHeight(102))),  # 'Working' label (when enabled)
                        Button((scaleWidth(148), scaleHeight(110), scaleWidth(22), scaleHeight(22)))],  # Spinner (when enabled)

    # Remaining screens are settings modes

    # Screen mode 4 is storage settings
    Screen.SETTINGS_STORAGE: [Button((0, scaleHeight(188), scaleWidth(320), scaleHeight(52))),  # We don't need the done button anymore, but the layout is hardcoded
                              Button((0, 0, scaleWidth(80), scaleHeight(52)),
                                     bg='prev', cb=settingCallback, value=-1),
                              Button((scaleWidth(240), 0, scaleWidth(80), scaleHeight(52)),
                                     bg='next', cb=settingCallback, value=1),
                              Button((scaleWidth(2), scaleHeight(60), scaleWidth(100), scaleHeight(120)), bg='radio3-1', fg='store-folder',
                                     cb=storeModeCallback, value=0),
                              Button((scaleWidth(110), scaleHeight(60), scaleWidth(100), scaleHeight(120)), bg='radio3-0', fg='store-boot',
                                     cb=storeModeCallback, value=1),
                              Button((scaleWidth(218), scaleHeight(60), scaleWidth(100), scaleHeight(120)), bg='radio3-0', fg='store-dropbox',
                                     cb=storeModeCallback, value=2),
                              Button((0, scaleHeight(10), scaleWidth(320), scaleHeight(35)), bg='storage')],

    # Screen mode 5 is size settings
    Screen.SETTINGS_SIZE: [Button((0, scaleHeight(188), scaleWidth(320), scaleHeight(52))),  # We don't need the done button anymore, but the layout is hardcoded
                           Button((0, 0, scaleWidth(80), scaleHeight(52)),
                                  bg='prev', cb=settingCallback, value=-1),
                           Button((scaleWidth(240), 0, scaleWidth(80), scaleHeight(52)),
                                  bg='next', cb=settingCallback, value=1),
                           Button((scaleWidth(2), scaleHeight(60), scaleWidth(100), scaleHeight(120)), bg='radio3-1', fg='size-l',
                                  cb=sizeModeCallback, value=0),
                           Button((scaleWidth(110), scaleHeight(60), scaleWidth(100), scaleHeight(120)), bg='radio3-0', fg='size-m',
                                  cb=sizeModeCallback, value=1),
                           Button((scaleWidth(218), scaleHeight(60), scaleWidth(100), scaleHeight(120)), bg='radio3-0', fg='size-s',
                                  cb=sizeModeCallback, value=2),
                           Button((0, scaleHeight(10), scaleWidth(320), scaleHeight(29)), bg='size')],

    # Screen mode 6 is graphic effect
    Screen.SETTINGS_EFFECT: [Button((0, scaleHeight(188), scaleWidth(320), scaleHeight(52))),  # We don't need the done button anymore, but the layout is hardcoded:
                             Button((0, 0, scaleWidth(80), scaleHeight(52)),
                                    bg='prev', cb=settingCallback, value=-1),
                             Button((scaleWidth(240), 0, scaleWidth(80), scaleHeight(52)), 
                                    bg='prev', cb=fxCallback, value=-1),
                             Button((scaleWidth(240), scaleHeight(70), scaleWidth(80),
                                     scaleHeight(52)), bg='next', cb=fxCallback, value=1),
                             Button((0, scaleHeight(67), scaleWidth(
                                 320), scaleHeight(91)), bg='fx-none'),
                             Button((0, scaleHeight(11), scaleWidth(320), scaleHeight(29)), bg='fx')],

    # Screen mode 7 is ISO
    Screen.SETTINGS_ISO: [Button((0, scaleHeight(188), scaleWidth(320), scaleHeight(52)), bg='done', cb=doneCallback),
                          Button((0, 0, scaleWidth(80), scaleHeight(52)),
                                 bg='prev', cb=settingCallback, value=-1),
                          Button((scaleWidth(240), 0, scaleWidth(80), scaleHeight(52)),
                                 bg='next', cb=settingCallback, value=1),
                          Button((0, scaleHeight(70), scaleWidth(80), scaleHeight(52)),
                                 bg='prev', cb=isoCallback, value=-1),
                          Button((scaleWidth(240), scaleHeight(70), scaleWidth(80),
                                  scaleHeight(52)), bg='next', cb=isoCallback, value=1),
                          Button((0, scaleHeight(79), scaleWidth(
                              320), scaleHeight(33)), bg='iso-0'),
                          Button((scaleWidth(9), scaleHeight(134), scaleWidth(
                              302), scaleHeight(26)), bg='iso-bar'),
                          Button((0, scaleHeight(157), scaleWidth(
                              21), scaleHeight(19)), bg='iso-arrow'),
                          Button((0, scaleHeight(10), scaleWidth(320), scaleHeight(29)), bg='iso')],

    # Screen mode 8 is EV Compensation
    Screen.SETTINGS_EV: [Button((0, scaleHeight(188), scaleWidth(320), scaleHeight(52)), bg='done', cb=doneCallback),
                         Button((0, 0, scaleWidth(80), scaleHeight(52)),
                                bg='prev', cb=settingCallback, value=-1),
                         Button((scaleWidth(240), 0, scaleWidth(80), scaleHeight(52)),
                                bg='next', cb=settingCallback, value=1),
                         Button((0, scaleHeight(70), scaleWidth(80), scaleHeight(52)),
                                bg='prev', cb=evCallback, value=-1),
                         Button((scaleWidth(240), scaleHeight(70), scaleWidth(80),
                                 scaleHeight(52)), bg='next', cb=evCallback, value=1),
                         Button((0, scaleHeight(79), scaleWidth(
                             320), scaleHeight(33)), bg='iso-0'),
                         Button((scaleWidth(9), scaleHeight(134), scaleWidth(
                             302), scaleHeight(26)), bg='ev-bar'),
                         Button((0, scaleHeight(157), scaleWidth(
                             21), scaleHeight(19)), bg='iso-arrow'),
                         Button((0, scaleHeight(10), scaleWidth(320), scaleHeight(29)), bg='ev')],

    # Screen mode 9 is quit confirmation
    Screen.QUIT: [  # Button((0, scaleHeight(188), scaleWidth(320), scaleHeight(52)), bg='done', cb=doneCallback),
                        Button((0, 0, scaleWidth(80), scaleHeight(52)),
                            bg='prev', cb=settingCallback, value=-1),
                        Button((scaleWidth(240), 0, scaleWidth(80), scaleHeight(52)),
                            bg='next', cb=settingCallback, value=1),
                        Button((scaleWidth(110), scaleHeight(60), scaleWidth(100),
                            scaleHeight(120)), bg='quit-ok', cb=quitCallback),
                        Button((0, scaleHeight(10), scaleWidth(320), scaleHeight(35)), bg='quit')]
})

# Assorted utility functions -----------------------------------------------

# Doesn't do anything at the moment


def setFxMode(n):
    global fxMode
    fxMode = n
# camera.image_effect = fxData[fxMode]
    buttons.get(Screen.SETTINGS_EFFECT)[5].setBg('fx-' + fxData[fxMode])


def setIsoMode(n):
    global isoMode
    try:
        isoMode = n
        # pycamera2 deals with analogue and digital gain, not ISO
        if isoMode > 0:
            camera.controls.AnalogueGain = math.log2(isoData[isoMode][0]/25)
        # Only works when auto exposure is off, 0 for Auto
        camera.controls.AeEnable = isoMode == 0
        buttons.get(Screen.SETTINGS_ISO)[5].setBg(
            'iso-' + str(isoData[isoMode][0]))
        buttons.get(Screen.SETTINGS_ISO)[7].rect = ((scaleWidth(isoData[isoMode][1] - 10),) +
                                                    buttons.get(Screen.SETTINGS_ISO)[7].rect[1:])
    except:
        print("Could not change ISO mode")
        # For some reason changes to the settings sometimes break with a key error!


def setEvMode(n):
    global evMode
    try:
        evMode = n
        camera.controls.ExposureValue = evData[evMode][0]/2.0
        # Only seems to work when auto exposure is on
        camera.controls.AeEnable = True
        buttons.get(Screen.SETTINGS_EV)[5].setBg(
            'ev-' + str(evData[evMode][0]))
        buttons.get(Screen.SETTINGS_EV)[7].rect = ((scaleWidth(evData[evMode][1] - 10),) +
                                                   buttons.get(Screen.SETTINGS_EV)[7].rect[1:])
    except:
        print("Could not change EV Mode")
        # For some reason changes to the settings sometimes break with a key error!

def setZoomMode(mode):
    (x_offset, y_offset, width, height) = camera.camera_properties['ScalerCropMaximum']
    zoom_factor = 4 # you can't tell if something is focused in 1:1 mapping, so let's scale
    factor_width = screen_width * zoom_factor
    factor_height = screen_height * zoom_factor
    if mode == ZoomMode.NORMAL:
        camera.controls.ScalerCrop = (x_offset, y_offset, width, height)
    elif mode == ZoomMode.ZOOMED:
        camera.controls.ScalerCrop = (int((width-factor_width)/2), int((height-factor_height)/2), factor_width, factor_height)

def saveSettings():
    try:
        outfile = open('cam.pkl', 'wb')
        # Use a dictionary (rather than pickling 'raw' values) so
        # the number & order of things can change without breaking.
        d = {'fx': fxMode,
             'iso': isoMode,
             'size': sizeMode,
             'store': storeMode,
             'ev': evMode}
        pickle.dump(d, outfile)
        outfile.close()
    except BaseException:
        pass


def loadSettings():
    global sizeMode
    try:
        infile = open('cam.pkl', 'rb')
        d = pickle.load(infile)
        infile.close()
        if 'fx' in d:
            setFxMode(d['fx'])
        if 'iso' in d:
            setIsoMode(d['iso'])
        if 'size' in d:
            setSizeModeAndButtons(d['size']) 
        if 'store' in d:
            storeModeCallback(d['store'])
        if 'ev' in d:
            setEvMode(d['ev'])
    except BaseException:
        pass

# Scan files in a directory, locating JPEGs with names matching the
# software's convention (IMG_XXXX.JPG), returning a tuple with the
# lowest and highest indices (or None if no matching files).
def imgRange(path):
    min = 9999
    max = 0
    try:
        for file in os.listdir(path):
            if fnmatch.fnmatch(file, 'IMG_[0-9][0-9][0-9][0-9].JPG'):
                i = int(file[4:8])
                if (i < min):
                    min = i
                if (i > max):
                    max = i
    finally:
        return None if min > max else (min, max)

def takePicture():
    global busy, gid, loadIdx, saveIdx, scaled, sizeMode, storeMode, storeModePrior, uid, screen_height, screen_width

    if not os.path.isdir(pathData[storeMode]):
        try:
            os.makedirs(pathData[storeMode])
            # Set new directory ownership to pi user, mode to 755
            os.chown(pathData[storeMode], uid, gid)
            os.chmod(pathData[storeMode],
                     stat.S_IRUSR | stat.S_IWUSR | stat.S_IXUSR |
                     stat.S_IRGRP | stat.S_IXGRP |
                     stat.S_IROTH | stat.S_IXOTH)
        except OSError as e:
            # errno = 2 if can't create folder
            print(errno.errorcode[e.errno])
            return

    # If this is the first time accessing this directory,
    # scan for the max index, start at next pos.
    if storeMode != storeModePrior:
        r = imgRange(pathData[storeMode])
        if r is None:
            saveIdx = 1
        else:
            saveIdx = r[1] + 1
            if saveIdx > 9999:
                saveIdx = 0
        storeModePrior = storeMode

    # Scan for next available image slot
    while True:
        filename = pathData[storeMode] + '/IMG_' + '%04d' % saveIdx + '.JPG'
        if not os.path.isfile(filename):
            break
        saveIdx += 1
        if saveIdx > 9999:
            saveIdx = 0

    t = threading.Thread(target=spinner)
    t.start()

    scaled = None
    try:
        request = camera.capture_request()
        # camera.capture_file(filename, format='jpeg')
        img = request.make_image('main')
        request.release()
        print("Request released")
        # Set image file ownership to pi user, mode to 644
        # os.chown(filename, uid, gid) # Not working, why?
        # os.chmod(filename, stat.S_IRUSR | stat.S_IWUSR | stat.S_IRGRP | stat.S_IROTH)
        # img = pygame.image.load(filename)
        mode = img.mode
        size = img.size
        data = img.tobytes()
        py_image = pygame.image.fromstring(data, size, mode)
        scaled = pygame.transform.scale(py_image, sizeData[sizeMode][1])
        print("Transform complete")
        img.save(filename)
        print("Save complete")
        # Set image file ownership to pi user, mode to 644
        # os.chown(filename, uid, gid) # Not working, why?
        os.chmod(filename, stat.S_IRUSR | stat.S_IWUSR | stat.S_IRGRP | stat.S_IROTH)
    finally:
        # Add error handling/indicator (disk full, etc.)
        busy = False
        t.join()

    pygame.display.update()
    loadIdx = saveIdx


# Initialization -----------------------------------------------------------
# Init framebuffer/touchscreen environment variables
os.putenv('SDL_VIDEODRIVER', 'fbcon')
os.putenv('SDL_FBDEV', '/dev/fb0')
# !!!!!!!ATTENTION!!!!!!!!
# When attached to an HDMI monitor, your TFT display will be /dev/fb1
# When operating on its own, your TFT display will be /dev/fb0
# To run in a desktop window, comment out the SDL_VIDEODRIVER and SDL_FBDEV settings
# And disable fullscreen below
# os.putenv('SDL_MOUSEDRV', 'TSLIB')
# os.putenv('SDL_MOUSEDEV', '/dev/input/event3')
os.putenv('SDL_NOMOUSE', '1')


# Get user & group IDs for file & folder creation
# (Want these to be 'pi' or other user, not root)
s = os.getenv("SUDO_UID")
uid = int(s) if s else os.getuid()
s = os.getenv("SUDO_GID")
gid = int(s) if s else os.getgid()


# Init camera and set up default values
res = (screen_width, screen_height)

# Init pygame and screen
pygame.init()
screen = pygame.display.set_mode((0, 0), pygame.FULLSCREEN)
# Uncomment to run in a window on a desktop instead
# screen = pygame.display.set_mode(res)
pygame.mouse.set_visible(False)

BACKGROUND = (0, 0, 0)
TEXTCOLOUR = (255, 255, 255)
# set up Fonts
fontObj = pygame.font.Font(None, 32)
textSufaceObj = fontObj.render('Loading assets', True, TEXTCOLOUR, None)
screen.blit(textSufaceObj, (0, int(screen_height/2)))
pygame.display.update()

# Load all icons at startup.
for file in os.listdir(iconPath):
    if fnmatch.fnmatch(file, '*.png'):
        icons.append(Icon(file.split('.')[0]))

# Assign Icons to Buttons, now that they're loaded
for s in buttons.values():        # For each screenful of buttons...
    for b in s:  # For each button on screen...
        for i in icons:  # For each icon...
            if b.bg == i.name:  # Compare names; match?
                b.iconBg = i  # Assign Icon to Button
                b.bg = None  # Name no longer used; allow garbage collection
            if b.fg == i.name:
                b.iconFg = i
                b.fg = None

screen.fill(0)
t = threading.Thread(target=spinner)
t.start()

# Set up Camera
# Tuning file for the Raspberry Pi HQ Camera
tuning = Picamera2.load_tuning_file("imx477.json")
camera = Picamera2(tuning=tuning)
main_config = {"size": sizeData[sizeMode][0]}
lores_config = {"size": sizeData[sizeMode][1]}

still_config = camera.create_still_configuration(main_config, lores_config)
camera.configure(still_config)
camera.still_configuration.enable_lores()
# Who knows why, but without setting the resolution here a second time I just get an empty screen
camera.still_configuration.lores.size = sizeData[sizeMode][1]
camera.still_configuration.align()
camera.start()

# I want my photos to be black and white and grainy. If you don't want that, remove these two lines
camera.controls.Saturation = 0.0
camera.controls.NoiseReductionMode = controls.draft.NoiseReductionModeEnum.Off

# Set up buttons

atexit.register(camera.stop)



loadSettings()  # Must come last; fiddles with Button/Icon states

screens = ['playback', 'delete_confirmation', '']

# This array defines the custom function of the keyboard buttons for each
# screen
controls = dict({
    Screen.VIEW: dict({pygame.K_LEFT: (imageCallback, -1),
                       pygame.K_RIGHT: (imageCallback, 1),
                       pygame.K_RETURN: (imageCallback, 0)
                       }),  # 0 is photo playback
    Screen.DELETE: dict({pygame.K_LEFT: (deleteCallback, True),
                         pygame.K_RIGHT: (deleteCallback, False)
                         }),  # 1 is delete confirmation
    Screen.NO_IMG: dict({}),  # 2 is photo playback if no images are available
    # 3 is viewfinder mode
    Screen.VIEWFINDER: dict({pygame.K_a: (takePicture, None),
                             pygame.K_RIGHT: (zoomModeCallback, None)}),
    Screen.SETTINGS_STORAGE: dict({}),  # 4 is storage settings
    Screen.SETTINGS_SIZE: dict({pygame.K_RIGHT: (sizeModeCallback, 1),
                                pygame.K_LEFT: (sizeModeCallback, -1)
                                }),  # 5 is size settings
    Screen.SETTINGS_EFFECT: dict({pygame.K_RIGHT: (fxCallback, 1),
                                  pygame.K_LEFT: (fxCallback, -1)
                                  }),  # 6 is effects settings
    Screen.SETTINGS_ISO: dict({pygame.K_RIGHT: (isoCallback, 1),
                               pygame.K_LEFT: (isoCallback, -1)
                               }),  # 7 is ISO settings
    Screen.SETTINGS_EV: dict({pygame.K_RIGHT: (evCallback, 1),
                              pygame.K_LEFT: (evCallback, -1)
                              }),  # 8 is EV settings
    Screen.QUIT: dict({pygame.K_RETURN: (quitCallback, None)}
                      )  # 9 is the quit screen
})

# Main loop ----------------------------------------------------------------
busy = False
t.join()
while (True):

    # Process touchscreen input
    while True:
        for event in pygame.event.get():
            if (event.type is KEYDOWN):
                # Execute the appropriate function for this key in the controls
                # array
                callbackTuple = controls.get(screenMode).get(event.key, None)
                if callbackTuple:
                    if callbackTuple[1] is not None:
                        callbackTuple[0](callbackTuple[1])
                    else:
                        callbackTuple[0]()
            # Some keys have default meaning if not overwritten
                if event.key == pygame.K_DOWN:
                    settingCallback(-1)
                elif event.key == pygame.K_UP:
                    settingCallback(1)
                elif event.key == pygame.K_z:  # Always have a backup key to quit out of the program in development
                    quitCallback()
                elif event.key == pygame.K_a:  # Return to camera mode if shutter button is pressed
                    doneCallback()
        # If in viewfinder or settings modes, stop processing touchscreen
        # and refresh the display to show the live preview.  In other modes
        # (image playback, etc.), stop and refresh the screen only when
        # screenMode changes.
        if screenMode.value >= 3 or screenMode != screenModePrior:
            break

    # Refresh display
    if screenMode.value >= 3:  # Viewfinder or settings modes
        yuv420 = camera.capture_array("lores")
        rgb = cv2.cvtColor(yuv420, cv2.COLOR_YUV420p2BGR)
        # The use of BGR here is intentional, for some reason the colours are wrong otherwise.

        # Dimensions of the output buffer might not be the same as the input. Surprise!
        h, w, d = rgb.shape
        img = pygame.image.frombuffer(rgb, (w, h), 'RGB')
        if pygame.display.get_init():
            screen.fill(0)
            img = pygame.transform.rotate(img, screen_rotation)
            fillBlit((0, 0, screen_width, screen_height), img, screen, True)
    elif screenMode.value < 2:  # Playback mode or delete confirmation
        img = scaled       # Show last-loaded image
        screen.fill(0)
        if (img):
            img = pygame.transform.rotate(img, screen_rotation)
            fitBlit((0, 0, screen_width, screen_height), img, screen, True)
    else:                # 'No Photos' mode
        img = None         # You get nothing, good day sir

    # Overlay buttons on display and update
    for i, b in enumerate(buttons.get(screenMode)):
        b.draw(screen)
    pygame.display.update()

    screenModePrior = screenMode